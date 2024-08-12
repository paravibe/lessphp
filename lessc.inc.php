<?php

/**
 * @file
 * Lessphp v0.5.1
 * http://leafo.net/lessphp
 *
 * LESS CSS compiler, adapted from http://lesscss.org.
 *
 * Copyright 2013, Leaf Corcoran <leafot@gmail.com>
 * Licensed under MIT or GPLv3, see LICENSE
 */

/**
 * The LESS compiler and parser.
 *
 * Converting LESS to CSS is a three stage process. The incoming file is parsed
 * by `lessc_parser` into a syntax tree, then it is compiled into another tree
 * representing the CSS structure by `lessc`. The CSS tree is fed into a
 * formatter, like `lessc_formatter` which then outputs CSS as a string.
 *
 * During the first compile, all values are *reduced*, which means that their
 * types are brought to the lowest form before being dump as strings. This
 * handles math equations, variable dereferences, and the like.
 *
 * The `parse` function of `lessc` is the entry point.
 *
 * In summary:
 *
 * The `lessc` class creates an instance of the parser, feeds it LESS code,
 * then transforms the resulting tree to a CSS tree. This class also holds the
 * evaluation context, such as all available mixins and variables at any given
 * time.
 *
 * The `lessc_parser` class is only concerned with parsing its input.
 *
 * The `lessc_formatter` takes a CSS tree, and dumps it to a formatted string,
 * handling things like indentation.
 */
class lessc {
  static public $VERSION = "v0.5.0";

  static public $TRUE = ["keyword", "true"];
  static public $FALSE = ["keyword", "false"];

  protected $libFunctions = [];
  protected $registeredVars = [];
  protected $preserveComments = FALSE;

  /**
   * Prefix of abstract properties.
   */
  public $vPrefix = '@';
  /**
   * Prefix of abstract blocks.
   */
  public $mPrefix = '$';
  public $parentSelector = '&';

  public $importDisabled = FALSE;
  public $importDir = '';

  protected $numberPrecision = NULL;

  protected $allParsedFiles = [];

  // Set to the parser that generated the current line when compiling.
  /**
   * So we know how to create error messages.
   */
  protected $sourceParser = NULL;
  protected $sourceLoc = NULL;

  /**
   * Uniquely identify imports.
   */
  static protected $nextImportId = 0;

  private ?stdclass $env;

  private mixed $_parseFile;

  private lessc_parser $parser;

  private ?stdclass $scope;

  /**
   * @var \lessc_formatter_lessjs|mixed
   */
  private mixed $formatter;

  private mixed $formatterName;

  /**
   * Attempts to find the path of an import url, returns null for css files.
   */
  protected function findImport($url) {
    foreach ((array) $this->importDir as $dir) {
      $full = $dir . (substr($dir, -1) != '/' ? '/' : '') . $url;
      if ($this->fileExists($file = $full . '.less') || $this->fileExists($file = $full)) {
        return $file;
      }
    }

    return NULL;
  }

  /**
   *
   */
  protected function fileExists($name) {
    return is_file($name);
  }

  /**
   *
   */
  public static function compressList($items, $delim) {
    if (!isset($items[1]) && isset($items[0])) {
      return $items[0];
    }
    else {
      return ['list', $delim, $items];
    }
  }

  /**
   *
   */
  public static function preg_quote($what) {
    return preg_quote($what, '/');
  }

  /**
   *
   */
  protected function tryImport($importPath, $parentBlock, $out) {
    if ($importPath[0] == "function" && $importPath[1] == "url") {
      $importPath = $this->flattenList($importPath[2]);
    }

    $str = $this->coerceString($importPath);
    if ($str === NULL) {
      return FALSE;
    }

    $url = $this->compileValue($this->lib_e($str));

    // don't import if it ends in css.
    if (substr_compare($url, '.css', -4, 4) === 0) {
      return FALSE;
    }

    $realPath = $this->findImport($url);

    if ($realPath === NULL) {
      return FALSE;
    }

    if ($this->importDisabled) {
      return [FALSE, "/* import disabled */"];
    }

    if (isset($this->allParsedFiles[realpath($realPath)])) {
      return [FALSE, NULL];
    }

    $this->addParsedFile($realPath);
    $parser = $this->makeParser($realPath);
    $root = $parser->parse(file_get_contents($realPath));

    // Set the parents of all the block props.
    foreach ($root->props as $prop) {
      if ($prop[0] == "block") {
        $prop[1]->parent = $parentBlock;
      }
    }

    // Copy mixins into scope, set their parents
    // bring blocks from import into current block.
    // @todo need to mark the source parser these came from this file.
    foreach ($root->children as $childName => $child) {
      if (isset($parentBlock->children[$childName])) {
        $parentBlock->children[$childName] = array_merge(
              $parentBlock->children[$childName],
              $child);
      }
      else {
        $parentBlock->children[$childName] = $child;
      }
    }

    $pi = pathinfo($realPath);
    $dir = $pi["dirname"];

    [$top, $bottom] = $this->sortProps($root->props, TRUE);
    $this->compileImportedProps($top, $parentBlock, $out, $parser, $dir);

    return [TRUE, $bottom, $parser, $dir];
  }

  /**
   *
   */
  protected function compileImportedProps($props, $block, $out, $sourceParser, $importDir) {
    $oldSourceParser = $this->sourceParser;

    $oldImport = $this->importDir;

    // @todo this is because the importDir api is stupid
    $this->importDir = (array) $this->importDir;
    array_unshift($this->importDir, $importDir);

    foreach ($props as $prop) {
      $this->compileProp($prop, $block, $out);
    }

    $this->importDir = $oldImport;
    $this->sourceParser = $oldSourceParser;
  }

  /**
   * Recursively compiles a block.
   *
   * A block is analogous to a CSS block in most cases. A single LESS document
   * is encapsulated in a block when parsed, but it does not have parent tags
   * so all of it's children appear on the root level when compiled.
   *
   * Blocks are made up of props and children.
   *
   * Props are property instructions, array tuples which describe an action
   * to be taken, eg. write a property, set a variable, mixin a block.
   *
   * The children of a block are just all the blocks that are defined within.
   * This is used to look up mixins when performing a mixin.
   *
   * Compiling the block involves pushing a fresh environment on the stack,
   * and iterating through the props, compiling each one.
   *
   * See lessc::compileProp()
   */
  protected function compileBlock($block) {
    switch ($block->type) {
      case "root":
        $this->compileRoot($block);
        break;

      case NULL:
        $this->compileCSSBlock($block);
        break;

      case "media":
        $this->compileMedia($block);
        break;

      case "directive":
        $name = "@" . $block->name;
        if (!empty($block->value)) {
          $name .= " " . $this->compileValue($this->reduce($block->value));
        }

        $this->compileNestedBlock($block, [$name]);
        break;

      default:
        $this->throwError("unknown block type: $block->type\n");
    }
  }

  /**
   *
   */
  protected function compileCSSBlock($block) {
    $env = $this->pushEnv();

    $selectors = $this->compileSelectors($block->tags);
    $env->selectors = $this->multiplySelectors($selectors);
    $out = $this->makeOutputBlock(NULL, $env->selectors);

    $this->scope->children[] = $out;
    $this->compileProps($block, $out);

    // Mixins carry scope with them!
    $block->scope = $env;
    $this->popEnv();
  }

  /**
   *
   */
  protected function compileMedia($media) {
    $env = $this->pushEnv($media);
    $parentScope = $this->mediaParent($this->scope);

    $query = $this->compileMediaQuery($this->multiplyMedia($env));

    $this->scope = $this->makeOutputBlock($media->type, [$query]);
    $parentScope->children[] = $this->scope;

    $this->compileProps($media, $this->scope);

    if (count($this->scope->lines) > 0) {
      $orphanSelelectors = $this->findClosestSelectors();
      if (!is_null($orphanSelelectors)) {
        $orphan = $this->makeOutputBlock(NULL, $orphanSelelectors);
        $orphan->lines = $this->scope->lines;
        array_unshift($this->scope->children, $orphan);
        $this->scope->lines = [];
      }
    }

    $this->scope = $this->scope->parent;
    $this->popEnv();
  }

  /**
   *
   */
  protected function mediaParent($scope) {
    while (!empty($scope->parent)) {
      if (!empty($scope->type) && $scope->type != "media") {
        break;
      }
      $scope = $scope->parent;
    }

    return $scope;
  }

  /**
   *
   */
  protected function compileNestedBlock($block, $selectors) {
    $this->pushEnv($block);
    $this->scope = $this->makeOutputBlock($block->type, $selectors);
    $this->scope->parent->children[] = $this->scope;

    $this->compileProps($block, $this->scope);

    $this->scope = $this->scope->parent;
    $this->popEnv();
  }

  /**
   *
   */
  protected function compileRoot($root) {
    $this->pushEnv();
    $this->scope = $this->makeOutputBlock($root->type);
    $this->compileProps($root, $this->scope);
    $this->popEnv();
  }

  /**
   *
   */
  protected function compileProps($block, $out) {
    foreach ($this->sortProps($block->props) as $prop) {
      $this->compileProp($prop, $block, $out);
    }
    $out->lines = $this->deduplicate($out->lines);
  }

  /**
   * Deduplicate lines in a block. Comments are not deduplicated. If a
   * duplicate rule is detected, the comments immediately preceding each
   * occurence are consolidated.
   */
  protected function deduplicate($lines) {
    $unique = [];
    $comments = [];

    foreach ($lines as $line) {
      if (strpos($line, '/*') === 0) {
        $comments[] = $line;
        continue;
      }
      if (!in_array($line, $unique)) {
        $unique[] = $line;
      }
      array_splice($unique, array_search($line, $unique), 0, $comments);
      $comments = [];
    }
    return array_merge($unique, $comments);
  }

  /**
   *
   */
  protected function sortProps($props, $split = FALSE) {
    $vars = [];
    $imports = [];
    $other = [];
    $stack = [];

    foreach ($props as $prop) {
      switch ($prop[0]) {
        case "comment":
          $stack[] = $prop;
          break;

        case "assign":
          $stack[] = $prop;
          if (isset($prop[1][0]) && $prop[1][0] == $this->vPrefix) {
            $vars = array_merge($vars, $stack);
          }
          else {
            $other = array_merge($other, $stack);
          }
          $stack = [];
          break;

        case "import":
          $id = self::$nextImportId++;
          $prop[] = $id;
          $stack[] = $prop;
          $imports = array_merge($imports, $stack);
          $other[] = ["import_mixin", $id];
          $stack = [];
          break;

        default:
          $stack[] = $prop;
          $other = array_merge($other, $stack);
          $stack = [];
          break;
      }
    }
    $other = array_merge($other, $stack);

    if ($split) {
      return [array_merge($imports, $vars), $other];
    }
    else {
      return array_merge($imports, $vars, $other);
    }
  }

  /**
   *
   */
  protected function compileMediaQuery($queries) {
    $compiledQueries = [];
    foreach ($queries as $query) {
      $parts = [];
      foreach ($query as $q) {
        switch ($q[0]) {
          case "mediaType":
            $parts[] = implode(" ", array_slice($q, 1));
            break;

          case "mediaExp":
            if (isset($q[2])) {
              $parts[] = "($q[1]: " .
                            $this->compileValue($this->reduce($q[2])) . ")";
            }
            else {
              $parts[] = "($q[1])";
            }
            break;

          case "variable":
            $parts[] = $this->compileValue($this->reduce($q));
            break;
        }
      }

      if (count($parts) > 0) {
        $compiledQueries[] = implode(" and ", $parts);
      }
    }

    $out = "@media";
    if (!empty($parts)) {
      $out .= " " .
                implode($this->formatter->selectorSeparator, $compiledQueries);
    }
    return $out;
  }

  /**
   *
   */
  protected function multiplyMedia($env, $childQueries = NULL) {
    if (is_null($env) ||
          !empty($env->block->type) && $env->block->type != "media"
      ) {
      return $childQueries;
    }

    // Plain old block, skip.
    if (empty($env->block->type)) {
      return $this->multiplyMedia($env->parent, $childQueries);
    }

    $out = [];
    $queries = $env->block->queries;
    if (is_null($childQueries)) {
      $out = $queries;
    }
    else {
      foreach ($queries as $parent) {
        foreach ($childQueries as $child) {
          $out[] = array_merge($parent, $child);
        }
      }
    }

    return $this->multiplyMedia($env->parent, $out);
  }

  /**
   *
   */
  protected function expandParentSelectors(&$tag, $replace) {
    $parts = explode("$&$", $tag);
    $count = 0;
    foreach ($parts as &$part) {
      $part = str_replace($this->parentSelector, $replace, $part, $c);
      $count += $c;
    }
    $tag = implode($this->parentSelector, $parts);
    return $count;
  }

  /**
   *
   */
  protected function findClosestSelectors() {
    $env = $this->env;
    $selectors = NULL;
    while ($env !== NULL) {
      if (isset($env->selectors)) {
        $selectors = $env->selectors;
        break;
      }
      $env = $env->parent;
    }

    return $selectors;
  }

  /**
   * Multiply $selectors against the nearest selectors in env.
   */
  protected function multiplySelectors($selectors) {
    // Find parent selectors.
    $parentSelectors = $this->findClosestSelectors();
    if (is_null($parentSelectors)) {
      // Kill parent reference in top level selector.
      foreach ($selectors as &$s) {
        $this->expandParentSelectors($s, "");
      }

      return $selectors;
    }

    $out = [];
    foreach ($parentSelectors as $parent) {
      foreach ($selectors as $child) {
        $count = $this->expandParentSelectors($child, $parent);

        // don't prepend the parent tag if & was used.
        if ($count > 0) {
          $out[] = trim($child);
        }
        else {
          $out[] = trim($parent . ' ' . $child);
        }
      }
    }

    return $out;
  }

  /**
   * Reduces selector expressions.
   */
  protected function compileSelectors($selectors) {
    $out = [];

    foreach ($selectors as $s) {
      if (is_array($s)) {
        [, $value] = $s;
        $out[] = trim($this->compileValue($this->reduce($value)));
      }
      else {
        $out[] = $s;
      }
    }

    return $out;
  }

  /**
   *
   */
  protected function eq($left, $right) {
    return $left == $right;
  }

  /**
   *
   */
  protected function patternMatch($block, $orderedArgs, $keywordArgs) {
    // Match the guards if it has them
    // any one of the groups must have all its guards pass for a match.
    if (!empty($block->guards)) {
      $groupPassed = FALSE;
      foreach ($block->guards as $guardGroup) {
        foreach ($guardGroup as $guard) {
          $this->pushEnv();
          $this->zipSetArgs($block->args, $orderedArgs, $keywordArgs);

          $negate = FALSE;
          if ($guard[0] == "negate") {
            $guard = $guard[1];
            $negate = TRUE;
          }

          $passed = $this->reduce($guard) == self::$TRUE;
          if ($negate) {
            $passed = !$passed;
          }

          $this->popEnv();

          if ($passed) {
            $groupPassed = TRUE;
          }
          else {
            $groupPassed = FALSE;
            break;
          }
        }

        if ($groupPassed) {
          break;
        }
      }

      if (!$groupPassed) {
        return FALSE;
      }
    }

    if (empty($block->args)) {
      return $block->isVararg || empty($orderedArgs) && empty($keywordArgs);
    }

    $remainingArgs = $block->args;
    if ($keywordArgs) {
      $remainingArgs = [];
      foreach ($block->args as $arg) {
        if ($arg[0] == "arg" && isset($keywordArgs[$arg[1]])) {
          continue;
        }

        $remainingArgs[] = $arg;
      }
    }

    // No args.
    $i = -1;
    // Try to match by arity or by argument literal.
    foreach ($remainingArgs as $i => $arg) {
      switch ($arg[0]) {
        case "lit":
          if (empty($orderedArgs[$i]) || !$this->eq($arg[1], $orderedArgs[$i])) {
            return FALSE;
          }
          break;

        case "arg":
          // No arg and no default value.
          if (!isset($orderedArgs[$i]) && !isset($arg[2])) {
            return FALSE;
          }
          break;

        case "rest":
          // Rest can be empty.
          $i--;
          break 2;
      }
    }

    if ($block->isVararg) {
      // Not having enough is handled above.
      return TRUE;
    }
    else {
      $numMatched = $i + 1;
      // Greater than because default values always match.
      return $numMatched >= count($orderedArgs);
    }
  }

  /**
   *
   */
  protected function patternMatchAll($blocks, $orderedArgs, $keywordArgs, $skip = []) {
    $matches = NULL;
    foreach ($blocks as $block) {
      // Skip seen blocks that don't have arguments.
      if (isset($skip[$block->id]) && !isset($block->args)) {
        continue;
      }

      if ($this->patternMatch($block, $orderedArgs, $keywordArgs)) {
        $matches[] = $block;
      }
    }

    return $matches;
  }

  /**
   * Attempt to find blocks matched by path and args.
   */
  protected function findBlocks($searchIn, $path, $orderedArgs, $keywordArgs, $seen = []) {
    if ($searchIn == NULL) {
      return NULL;
    }
    if (isset($seen[$searchIn->id])) {
      return NULL;
    }
    $seen[$searchIn->id] = TRUE;

    $name = $path[0];

    if (isset($searchIn->children[$name])) {
      $blocks = $searchIn->children[$name];
      if (count($path) == 1) {
        $matches = $this->patternMatchAll($blocks, $orderedArgs, $keywordArgs, $seen);
        if (!empty($matches)) {
          // This will return all blocks that match in the closest
          // scope that has any matching block, like lessjs.
          return $matches;
        }
      }
      else {
        $matches = [];
        foreach ($blocks as $subBlock) {
          $subMatches = $this->findBlocks($subBlock,
                array_slice($path, 1), $orderedArgs, $keywordArgs, $seen);

          if (!is_null($subMatches)) {
            foreach ($subMatches as $sm) {
              $matches[] = $sm;
            }
          }
        }

        return count($matches) > 0 ? $matches : NULL;
      }
    }
    if ($searchIn->parent === $searchIn) {
      return NULL;
    }
    return $this->findBlocks($searchIn->parent, $path, $orderedArgs, $keywordArgs, $seen);
  }

  // Sets all argument names in $args to either the default value.

  /**
   * Or the one passed in through $values.
   */
  protected function zipSetArgs($args, $orderedValues, $keywordValues) {
    $assignedValues = [];

    $i = 0;
    foreach ($args as $a) {
      if ($a[0] == "arg") {
        if (isset($keywordValues[$a[1]])) {
          // Has keyword arg.
          $value = $keywordValues[$a[1]];
        }
        elseif (isset($orderedValues[$i])) {
          // Has ordered arg.
          $value = $orderedValues[$i];
          $i++;
        }
        elseif (isset($a[2])) {
          // Has default value.
          $value = $a[2];
        }
        else {
          $this->throwError("Failed to assign arg " . $a[1]);
          // :(
          $value = NULL;
        }

        $value = $this->reduce($value);
        $this->set($a[1], $value);
        $assignedValues[] = $value;
      }
      else {
        // A lit.
        $i++;
      }
    }

    // Check for a rest.
    if (!empty($args)) {
      $last = end($args);
      if ($last[0] == "rest") {
        $rest = array_slice($orderedValues, count($args) - 1);
        $this->set($last[1], $this->reduce(["list", " ", $rest]));
      }
    }

    // Wow is this the only true use of PHP's + operator for arrays?
    $this->env->arguments = $assignedValues + $orderedValues;
  }

  /**
   * Compile a prop and update $lines or $blocks appropriately.
   */
  protected function compileProp($prop, $block, $out) {
    // Set error position context.
    $this->sourceLoc = $prop[-1] ?? -1;

    switch ($prop[0]) {
      case 'assign':
        [, $name, $value] = $prop;
        if ($name[0] == $this->vPrefix) {
          $this->set($name, $value);
        }
        else {
          $out->lines[] = $this->formatter->property($name,
                    $this->compileValue($this->reduce($value)));
        }
        break;

      case 'block':
        [, $child] = $prop;
        $this->compileBlock($child);
        break;

      case 'mixin':
        [, $path, $args, $suffix] = $prop;

        $orderedArgs = [];
        $keywordArgs = [];
        foreach ((array) $args as $arg) {
          $argval = NULL;
          switch ($arg[0]) {
            case "arg":
              if (!isset($arg[2])) {
                $orderedArgs[] = $this->reduce(["variable", $arg[1]]);
              }
              else {
                $keywordArgs[$arg[1]] = $this->reduce($arg[2]);
              }
              break;

            case "lit":
              $orderedArgs[] = $this->reduce($arg[1]);
              break;

            default:
              $this->throwError("Unknown arg type: " . $arg[0]);
          }
        }

        $mixins = $this->findBlocks($block, $path, $orderedArgs, $keywordArgs);

        if ($mixins === NULL) {
          $this->throwError("{$prop[1][0]} is undefined");
        }

        foreach ($mixins as $mixin) {
          if ($mixin === $block && !$orderedArgs) {
            continue;
          }

          $haveScope = FALSE;
          if (isset($mixin->parent->scope)) {
            $haveScope = TRUE;
            $mixinParentEnv = $this->pushEnv();
            $mixinParentEnv->storeParent = $mixin->parent->scope;
          }

          $haveArgs = FALSE;
          if (isset($mixin->args)) {
            $haveArgs = TRUE;
            $this->pushEnv();
            $this->zipSetArgs($mixin->args, $orderedArgs, $keywordArgs);
          }

          $oldParent = $mixin->parent;
          if ($mixin != $block) {
            $mixin->parent = $block;
          }

          foreach ($this->sortProps($mixin->props) as $subProp) {
            if ($suffix !== NULL &&
                  $subProp[0] == "assign" &&
                  is_string($subProp[1]) &&
                  $subProp[1][0] != $this->vPrefix
              ) {
              $subProp[2] = [
                'list', ' ',
                    [$subProp[2], ['keyword', $suffix]],
              ];
            }

            $this->compileProp($subProp, $mixin, $out);
          }

          $mixin->parent = $oldParent;

          if ($haveArgs) {
            $this->popEnv();
          }
          if ($haveScope) {
            $this->popEnv();
          }
        }

        break;

      case 'raw':
        $out->lines[] = $prop[1];
        break;

      case "directive":
        [, $name, $value] = $prop;
        $out->lines[] = "@$name " . $this->compileValue($this->reduce($value)) . ';';
        break;

      case "comment":
        $out->lines[] = $prop[1];
        break;

      case "import":
        [, $importPath, $importId] = $prop;
        $importPath = $this->reduce($importPath);

        if (!isset($this->env->imports)) {
          $this->env->imports = [];
        }

        $result = $this->tryImport($importPath, $block, $out);

        $this->env->imports[$importId] = $result === FALSE ?
                [FALSE, "@import " . $this->compileValue($importPath) . ";"] :
                $result;

        break;

      case "import_mixin":
        [, $importId] = $prop;
        $import = $this->env->imports[$importId];
        if ($import[0] === FALSE) {
          if (isset($import[1])) {
            $out->lines[] = $import[1];
          }
        }
        else {
          [, $bottom, $parser, $importDir] = $import;
          $this->compileImportedProps($bottom, $block, $out, $parser, $importDir);
        }

        break;

      default:
        $this->throwError("unknown op: {$prop[0]}\n");
    }
  }

  /**
   * Compiles a primitive value into a CSS property value.
   *
   * Values in lessphp are typed by being wrapped in arrays, their format is
   * typically:
   *
   *     array(type, contents [, additional_contents]*)
   *
   * The input is expected to be reduced. This function will not work on
   * things like expressions and variables.
   */
  public function compileValue($value) {
    switch ($value[0]) {
      case 'list':
        // [1] - delimiter
        // [2] - array of values
        return implode($value[1], array_map([$this, 'compileValue'], $value[2]));

      case 'raw_color':
        if (!empty($this->formatter->compressColors)) {
          return $this->compileValue($this->coerceColor($value));
        }
        return $value[1];

      case 'keyword':
        // [1] - the keyword
        return $value[1];

      case 'number':
        [, $num, $unit] = $value;
        // [1] - the number
        // [2] - the unit
        if ($this->numberPrecision !== NULL) {
          $num = round($num, $this->numberPrecision);
        }
        return $num . $unit;

      case 'string':
        // [1] - contents of string (includes quotes)
        [, $delim, $content] = $value;
        foreach ($content as &$part) {
          if (is_array($part)) {
            $part = $this->compileValue($part);
          }
        }
        return $delim . implode($content) . $delim;

      case 'color':
        // [1] - red component (either number or a %)
        // [2] - green component
        // [3] - blue component
        // [4] - optional alpha component
        [, $r, $g, $b] = $value;
        $r = round($r);
        $g = round($g);
        $b = round($b);

        // Rgba.
        if (count($value) == 5 && $value[4] != 1) {
          return 'rgba(' . $r . ',' . $g . ',' . $b . ',' . $value[4] . ')';
        }

        $h = sprintf("#%02x%02x%02x", $r, $g, $b);

        if (!empty($this->formatter->compressColors)) {
          // Converting hex color to short notation (e.g. #003399 to #039)
          if ($h[1] === $h[2] && $h[3] === $h[4] && $h[5] === $h[6]) {
            $h = '#' . $h[1] . $h[3] . $h[5];
          }
        }

        return $h;

      case 'function':
        [, $name, $args] = $value;
        return $name . '(' . $this->compileValue($args) . ')';

      // Assumed to be unit.
      default:
        $this->throwError("unknown value type: $value[0]");
    }
  }

  /**
   *
   */
  protected function lib_pow($args) {
    [$base, $exp] = $this->assertArgs($args, 2, "pow");
    return pow($this->assertNumber($base), $this->assertNumber($exp));
  }

  /**
   *
   */
  protected function lib_pi() {
    return pi();
  }

  /**
   *
   */
  protected function lib_mod($args) {
    [$a, $b] = $this->assertArgs($args, 2, "mod");
    return $this->assertNumber($a) % $this->assertNumber($b);
  }

  /**
   *
   */
  protected function lib_tan($num) {
    return tan($this->assertNumber($num));
  }

  /**
   *
   */
  protected function lib_sin($num) {
    return sin($this->assertNumber($num));
  }

  /**
   *
   */
  protected function lib_cos($num) {
    return cos($this->assertNumber($num));
  }

  /**
   *
   */
  protected function lib_atan($num) {
    $num = atan($this->assertNumber($num));
    return ["number", $num, "rad"];
  }

  /**
   *
   */
  protected function lib_asin($num) {
    $num = asin($this->assertNumber($num));
    return ["number", $num, "rad"];
  }

  /**
   *
   */
  protected function lib_acos($num) {
    $num = acos($this->assertNumber($num));
    return ["number", $num, "rad"];
  }

  /**
   *
   */
  protected function lib_sqrt($num) {
    return sqrt($this->assertNumber($num));
  }

  /**
   *
   */
  protected function lib_extract($value) {
    [$list, $idx] = $this->assertArgs($value, 2, "extract");
    $idx = $this->assertNumber($idx);
    // 1 indexed
    if ($list[0] == "list" && isset($list[2][$idx - 1])) {
      return $list[2][$idx - 1];
    }
  }

  /**
   *
   */
  protected function lib_isnumber($value) {
    return $this->toBool($value[0] == "number");
  }

  /**
   *
   */
  protected function lib_isstring($value) {
    return $this->toBool($value[0] == "string");
  }

  /**
   *
   */
  protected function lib_iscolor($value) {
    return $this->toBool($this->coerceColor($value));
  }

  /**
   *
   */
  protected function lib_iskeyword($value) {
    return $this->toBool($value[0] == "keyword");
  }

  /**
   *
   */
  protected function lib_ispixel($value) {
    return $this->toBool($value[0] == "number" && $value[2] == "px");
  }

  /**
   *
   */
  protected function lib_ispercentage($value) {
    return $this->toBool($value[0] == "number" && $value[2] == "%");
  }

  /**
   *
   */
  protected function lib_isem($value) {
    return $this->toBool($value[0] == "number" && $value[2] == "em");
  }

  /**
   *
   */
  protected function lib_isrem($value) {
    return $this->toBool($value[0] == "number" && $value[2] == "rem");
  }

  /**
   *
   */
  protected function lib_rgbahex($color) {
    $color = $this->coerceColor($color);
    if (is_null($color)) {
      $this->throwError("color expected for rgbahex");
    }

    return sprintf("#%02x%02x%02x%02x",
          isset($color[4]) ? $color[4] * 255 : 255,
          $color[1],
          $color[2],
          $color[3]
      );
  }

  /**
   *
   */
  protected function lib_argb($color) {
    return $this->lib_rgbahex($color);
  }

  /**
   * Given an url, decide whether to output a regular link or the base64-encoded contents of the file.
   *
   * @param array $value
   *   either an argument list (two strings) or a single string.
   *
   * @return string        formatted url(), either as a link or base64-encoded.
   */
  protected function lib_data_uri($value) {
    $mime = ($value[0] === 'list') ? $value[2][0][2] : NULL;
    $url = ($value[0] === 'list') ? $value[2][1][2][0] : $value[2][0];

    $fullpath = $this->findImport($url);

    if ($fullpath && ($fsize = filesize($fullpath)) !== FALSE) {
      // IE8 can't handle data uris larger than 32KB.
      if ($fsize / 1024 < 32) {
        if (is_null($mime)) {
          // Php 5.3+.
          if (class_exists('finfo')) {
            $finfo = new finfo(FILEINFO_MIME);
            $mime = explode('; ', $finfo->file($fullpath));
            $mime = $mime[0];
            // PHP 5.2.
          }
          elseif (function_exists('mime_content_type')) {
            $mime = mime_content_type($fullpath);
          }
        }

        // Fallback if the mime type is still unknown.
        if (!is_null($mime)) {
          $url = sprintf('data:%s;base64,%s', $mime, base64_encode(file_get_contents($fullpath)));
        }
      }
    }

    return 'url("' . $url . '")';
  }

  /**
   * Utility func to unquote a string.
   */
  protected function lib_e($arg) {
    switch ($arg[0]) {
      case "list":
        $items = $arg[2];
        if (isset($items[0])) {
          return $this->lib_e($items[0]);
        }
        $this->throwError("unrecognised input");
      case "string":
        $arg[1] = "";
        return $arg;

      case "keyword":
        return $arg;

      default:
        return ["keyword", $this->compileValue($arg)];
    }
  }

  /**
   *
   */
  protected function lib__sprintf($args) {
    if ($args[0] != "list") {
      return $args;
    }
    $values = $args[2];
    $string = array_shift($values);
    $template = $this->compileValue($this->lib_e($string));

    $i = 0;
    if (preg_match_all('/%[dsa]/', $template, $m)) {
      foreach ($m[0] as $match) {
        $val = isset($values[$i]) ?
                    $this->reduce($values[$i]) : ['keyword', ''];

        // Lessjs compat, renders fully expanded color, not raw color.
        if ($color = $this->coerceColor($val)) {
          $val = $color;
        }

        $i++;
        $rep = $this->compileValue($this->lib_e($val));
        $template = preg_replace('/' . self::preg_quote($match) . '/',
              $rep, $template, 1);
      }
    }

    $d = $string[0] == "string" ? $string[1] : '"';
    return ["string", $d, [$template]];
  }

  /**
   *
   */
  protected function lib_floor($arg) {
    $value = $this->assertNumber($arg);
    return ["number", floor($value), $arg[2]];
  }

  /**
   *
   */
  protected function lib_ceil($arg) {
    $value = $this->assertNumber($arg);
    return ["number", ceil($value), $arg[2]];
  }

  /**
   *
   */
  protected function lib_round($arg) {
    if ($arg[0] != "list") {
      $value = $this->assertNumber($arg);
      return ["number", round($value), $arg[2]];
    }
    else {
      $value = $this->assertNumber($arg[2][0]);
      $precision = $this->assertNumber($arg[2][1]);
      return ["number", round($value, $precision), $arg[2][0][2]];
    }
  }

  /**
   *
   */
  protected function lib_unit($arg) {
    if ($arg[0] == "list") {
      [$number, $newUnit] = $arg[2];
      return ["number", $this->assertNumber($number),
        $this->compileValue($this->lib_e($newUnit)),
      ];
    }
    else {
      return ["number", $this->assertNumber($arg), ""];
    }
  }

  /**
   * Helper function to get arguments for color manipulation functions.
   * takes a list that contains a color like thing and a percentage
   */
  public function colorArgs($args) {
    if ($args[0] != 'list' || count($args[2]) < 2) {
      return [['color', 0, 0, 0], 0];
    }
    [$color, $delta] = $args[2];
    $color = $this->assertColor($color);
    $delta = floatval($delta[1]);

    return [$color, $delta];
  }

  /**
   *
   */
  protected function lib_darken($args) {
    [$color, $delta] = $this->colorArgs($args);

    $hsl = $this->toHSL($color);
    $hsl[3] = $this->clamp($hsl[3] - $delta, 100);
    return $this->toRGB($hsl);
  }

  /**
   *
   */
  protected function lib_lighten($args) {
    [$color, $delta] = $this->colorArgs($args);

    $hsl = $this->toHSL($color);
    $hsl[3] = $this->clamp($hsl[3] + $delta, 100);
    return $this->toRGB($hsl);
  }

  /**
   *
   */
  protected function lib_saturate($args) {
    [$color, $delta] = $this->colorArgs($args);

    $hsl = $this->toHSL($color);
    $hsl[2] = $this->clamp($hsl[2] + $delta, 100);
    return $this->toRGB($hsl);
  }

  /**
   *
   */
  protected function lib_desaturate($args) {
    [$color, $delta] = $this->colorArgs($args);

    $hsl = $this->toHSL($color);
    $hsl[2] = $this->clamp($hsl[2] - $delta, 100);
    return $this->toRGB($hsl);
  }

  /**
   *
   */
  protected function lib_spin($args) {
    [$color, $delta] = $this->colorArgs($args);

    $hsl = $this->toHSL($color);

    $hsl[1] = $hsl[1] + $delta % 360;
    if ($hsl[1] < 0) {
      $hsl[1] += 360;
    }

    return $this->toRGB($hsl);
  }

  /**
   *
   */
  protected function lib_fadeout($args) {
    [$color, $delta] = $this->colorArgs($args);
    $color[4] = $this->clamp(($color[4] ?? 1) - $delta / 100);
    return $color;
  }

  /**
   *
   */
  protected function lib_fadein($args) {
    [$color, $delta] = $this->colorArgs($args);
    $color[4] = $this->clamp(($color[4] ?? 1) + $delta / 100);
    return $color;
  }

  /**
   *
   */
  protected function lib_hue($color) {
    $hsl = $this->toHSL($this->assertColor($color));
    return round($hsl[1]);
  }

  /**
   *
   */
  protected function lib_saturation($color) {
    $hsl = $this->toHSL($this->assertColor($color));
    return round($hsl[2]);
  }

  /**
   *
   */
  protected function lib_lightness($color) {
    $hsl = $this->toHSL($this->assertColor($color));
    return round($hsl[3]);
  }

  // Get the alpha of a color.

  /**
   * Defaults to 1 for non-colors or colors without an alpha.
   */
  protected function lib_alpha($value) {
    if (!is_null($color = $this->coerceColor($value))) {
      return $color[4] ?? 1;
    }
  }

  /**
   * Set the alpha of the color.
   */
  protected function lib_fade($args) {
    [$color, $alpha] = $this->colorArgs($args);
    $color[4] = $this->clamp($alpha / 100.0);
    return $color;
  }

  /**
   *
   */
  protected function lib_percentage($arg) {
    $num = $this->assertNumber($arg);
    return ["number", $num * 100, "%"];
  }

  /**
   * Mix color with white in variable proportion.
   *
   * It is the same as calling `mix(#ffffff, @color, @weight)`.
   *
   *     tint(@color, [@weight: 50%]);
   *
   * http://lesscss.org/functions/#color-operations-tint
   *
   * @return array Color
   */
  protected function lib_tint($args) {
    $white = ['color', 255, 255, 255];
    if ($args[0] == 'color') {
      return $this->lib_mix(['list', ',', [$white, $args]]);
    }
    elseif ($args[0] == "list" && count($args[2]) == 2) {
      return $this->lib_mix([$args[0], $args[1], [$white, $args[2][0], $args[2][1]]]);
    }
    else {
      $this->throwError("tint expects (color, weight)");
    }
  }

  /**
   * Mix color with black in variable proportion.
   *
   * It is the same as calling `mix(#000000, @color, @weight)`
   *
   *     shade(@color, [@weight: 50%]);
   *
   * http://lesscss.org/functions/#color-operations-shade
   *
   * @return array Color
   */
  protected function lib_shade($args) {
    $black = ['color', 0, 0, 0];
    if ($args[0] == 'color') {
      return $this->lib_mix(['list', ',', [$black, $args]]);
    }
    elseif ($args[0] == "list" && count($args[2]) == 2) {
      return $this->lib_mix([$args[0], $args[1], [$black, $args[2][0], $args[2][1]]]);
    }
    else {
      $this->throwError("shade expects (color, weight)");
    }
  }

  // Mixes two colors by weight
  // mix(@color1, @color2, [@weight: 50%]);.

  /**
   * Http://sass-lang.com/docs/yardoc/Sass/Script/Functions.html#mix-instance_method.
   */
  protected function lib_mix($args) {
    if ($args[0] != "list" || count($args[2]) < 2) {
      $this->throwError("mix expects (color1, color2, weight)");
    }

    [$first, $second] = $args[2];
    $first = $this->assertColor($first);
    $second = $this->assertColor($second);

    $first_a = $this->lib_alpha($first);
    $second_a = $this->lib_alpha($second);

    if (isset($args[2][2])) {
      $weight = $args[2][2][1] / 100.0;
    }
    else {
      $weight = 0.5;
    }

    $w = $weight * 2 - 1;
    $a = $first_a - $second_a;

    $w1 = (($w * $a == -1 ? $w : ($w + $a) / (1 + $w * $a)) + 1) / 2.0;
    $w2 = 1.0 - $w1;

    $new = ['color',
      $w1 * $first[1] + $w2 * $second[1],
      $w1 * $first[2] + $w2 * $second[2],
      $w1 * $first[3] + $w2 * $second[3],
    ];

    if ($first_a != 1.0 || $second_a != 1.0) {
      $new[] = $first_a * $weight + $second_a * ($weight - 1);
    }

    return $this->fixColor($new);
  }

  /**
   *
   */
  protected function lib_contrast($args) {
    $darkColor  = ['color', 0, 0, 0];
    $lightColor = ['color', 255, 255, 255];
    $threshold  = 0.43;

    if ($args[0] == 'list') {
      $inputColor = (isset($args[2][0])) ? $this->assertColor($args[2][0]) : $lightColor;
      $darkColor  = (isset($args[2][1])) ? $this->assertColor($args[2][1]) : $darkColor;
      $lightColor = (isset($args[2][2])) ? $this->assertColor($args[2][2]) : $lightColor;
      $threshold  = (isset($args[2][3])) ? $this->assertNumber($args[2][3]) : $threshold;
    }
    else {
      $inputColor = $this->assertColor($args);
    }

    $inputColor = $this->coerceColor($inputColor);
    $darkColor  = $this->coerceColor($darkColor);
    $lightColor = $this->coerceColor($lightColor);

    // Figure out which is actually light and dark!
    if ($this->toLuma($darkColor) > $this->toLuma($lightColor)) {
      $t = $lightColor;
      $lightColor = $darkColor;
      $darkColor  = $t;
    }

    $inputColor_alpha = $this->lib_alpha($inputColor);
    if (($this->toLuma($inputColor) * $inputColor_alpha) < $threshold) {
      return $lightColor;
    }
    return $darkColor;
  }

  /**
   *
   */
  private function toLuma($color) {
    [, $r, $g, $b] = $this->coerceColor($color);

    $r = $r / 255;
    $g = $g / 255;
    $b = $b / 255;

    $r = ($r <= 0.03928) ? $r / 12.92 : pow((($r + 0.055) / 1.055), 2.4);
    $g = ($g <= 0.03928) ? $g / 12.92 : pow((($g + 0.055) / 1.055), 2.4);
    $b = ($b <= 0.03928) ? $b / 12.92 : pow((($b + 0.055) / 1.055), 2.4);

    return (0.2126 * $r) + (0.7152 * $g) + (0.0722 * $b);
  }

  /**
   *
   */
  protected function lib_luma($color) {
    return ["number", round($this->toLuma($color) * 100, 8), "%"];
  }

  /**
   *
   */
  public function assertColor($value, $error = "expected color value") {
    $color = $this->coerceColor($value);
    if (is_null($color)) {
      $this->throwError($error);
    }
    return $color;
  }

  /**
   *
   */
  public function assertNumber($value, $error = "expecting number") {
    if ($value[0] == "number") {
      return $value[1];
    }
    $this->throwError($error);
  }

  /**
   *
   */
  public function assertArgs($value, $expectedArgs, $name = "") {
    if ($expectedArgs == 1) {
      return $value;
    }
    else {
      if ($value[0] !== "list" || $value[1] != ",") {
        $this->throwError("expecting list");
      }
      $values = $value[2];
      $numValues = count($values);
      if ($expectedArgs != $numValues) {
        if ($name) {
          $name = $name . ": ";
        }

        $this->throwError("{$name}expecting $expectedArgs arguments, got $numValues");
      }

      return $values;
    }
  }

  /**
   *
   */
  protected function toHSL($color) {
    if ($color[0] === 'hsl') {
      return $color;
    }

    $r = $color[1] / 255;
    $g = $color[2] / 255;
    $b = $color[3] / 255;

    $min = min($r, $g, $b);
    $max = max($r, $g, $b);

    $L = ($min + $max) / 2;
    if ($min == $max) {
      $S = $H = 0;
    }
    else {
      if ($L < 0.5) {
        $S = ($max - $min) / ($max + $min);
      }
      else {
        $S = ($max - $min) / (2.0 - $max - $min);
      }
      if ($r == $max) {
        $H = ($g - $b) / ($max - $min);
      }
      elseif ($g == $max) {
        $H = 2.0 + ($b - $r) / ($max - $min);
      }
      elseif ($b == $max) {
        $H = 4.0 + ($r - $g) / ($max - $min);
      }

    }

    $out = ['hsl',
      ($H < 0 ? $H + 6 : $H) * 60,
      $S * 100,
      $L * 100,
    ];

    if (count($color) > 4) {
      // Copy alpha.
      $out[] = $color[4];
    }
    return $out;
  }

  /**
   *
   */
  protected function toRGB_helper($comp, $temp1, $temp2) {
    if ($comp < 0) {
      $comp += 1.0;
    }
    elseif ($comp > 1) {
      $comp -= 1.0;
    }

    if (6 * $comp < 1) {
      return $temp1 + ($temp2 - $temp1) * 6 * $comp;
    }
    if (2 * $comp < 1) {
      return $temp2;
    }
    if (3 * $comp < 2) {
      return $temp1 + ($temp2 - $temp1) * ((2 / 3) - $comp) * 6;
    }

    return $temp1;
  }

  /**
   * Converts a hsl array into a color value in rgb.
   * Expects H to be in range of 0 to 360, S and L in 0 to 100
   */
  protected function toRGB($color) {
    if ($color[0] === 'color') {
      return $color;
    }

    $H = $color[1] / 360;
    $S = $color[2] / 100;
    $L = $color[3] / 100;

    if ($S == 0) {
      $r = $g = $b = $L;
    }
    else {
      $temp2 = $L < 0.5 ?
                $L * (1.0 + $S) :
                $L + $S - $L * $S;

      $temp1 = 2.0 * $L - $temp2;

      $r = $this->toRGB_helper($H + 1 / 3, $temp1, $temp2);
      $g = $this->toRGB_helper($H, $temp1, $temp2);
      $b = $this->toRGB_helper($H - 1 / 3, $temp1, $temp2);
    }

    // $out = array('color', round($r*255), round($g*255), round($b*255));
    $out = ['color', $r * 255, $g * 255, $b * 255];
    if (count($color) > 4) {
      // Copy alpha.
      $out[] = $color[4];
    }
    return $out;
  }

  /**
   *
   */
  protected function clamp($v, $max = 1, $min = 0) {
    return min($max, max($min, $v));
  }

  /**
   * Convert the rgb, rgba, hsl color literals of function type
   * as returned by the parser into values of color type.
   */
  protected function funcToColor($func) {
    $fname = $func[1];
    if ($func[2][0] != 'list') {
      // Need a list of arguments.
      return FALSE;
    }
    $rawComponents = $func[2][2];

    if ($fname == 'hsl' || $fname == 'hsla') {
      $hsl = ['hsl'];
      $i = 0;
      foreach ($rawComponents as $c) {
        $val = $this->reduce($c);
        $val = isset($val[1]) ? floatval($val[1]) : 0;

        if ($i == 0) {
          $clamp = 360;
        }
        elseif ($i < 3) {
          $clamp = 100;
        }
        else {
          $clamp = 1;
        }

        $hsl[] = $this->clamp($val, $clamp);
        $i++;
      }

      while (count($hsl) < 4) {
        $hsl[] = 0;
      }
      return $this->toRGB($hsl);

    }
    elseif ($fname == 'rgb' || $fname == 'rgba') {
      $components = [];
      $i = 1;
      foreach ($rawComponents as $c) {
        $c = $this->reduce($c);
        if ($i < 4) {
          if ($c[0] == "number" && $c[2] == "%") {
            $components[] = 255 * ($c[1] / 100);
          }
          else {
            $components[] = floatval($c[1]);
          }
        }
        elseif ($i == 4) {
          if ($c[0] == "number" && $c[2] == "%") {
            $components[] = 1.0 * ($c[1] / 100);
          }
          else {
            $components[] = floatval($c[1]);
          }
        }
        else {
          break;
        }

        $i++;
      }
      while (count($components) < 3) {
        $components[] = 0;
      }
      array_unshift($components, 'color');
      return $this->fixColor($components);
    }

    return FALSE;
  }

  /**
   *
   */
  protected function reduce($value, $forExpression = FALSE) {
    switch ($value[0]) {
      case "interpolate":
        $reduced = $this->reduce($value[1]);
        $var = $this->compileValue($reduced);
        $res = $this->reduce(["variable", $this->vPrefix . $var]);

        if ($res[0] == "raw_color") {
          $res = $this->coerceColor($res);
        }

        if (empty($value[2])) {
          $res = $this->lib_e($res);
        }

        return $res;

      case "variable":
        $key = $value[1];
        if (is_array($key)) {
          $key = $this->reduce($key);
          $key = $this->vPrefix . $this->compileValue($this->lib_e($key));
        }

        $seen =& $this->env->seenNames;

        if (!empty($seen[$key])) {
          $this->throwError("infinite loop detected: $key");
        }

        $seen[$key] = TRUE;
        $out = $this->reduce($this->get($key));
        $seen[$key] = FALSE;
        return $out;

      case "list":
        foreach ($value[2] as &$item) {
          $item = $this->reduce($item, $forExpression);
        }
        return $value;

      case "expression":
        return $this->evaluate($value);

      case "string":
        foreach ($value[2] as &$part) {
          if (is_array($part)) {
            $strip = $part[0] == "variable";
            $part = $this->reduce($part);
            if ($strip) {
              $part = $this->lib_e($part);
            }
          }
        }
        return $value;

      case "escape":
        [, $inner] = $value;
        return $this->lib_e($this->reduce($inner));

      case "function":
        $color = $this->funcToColor($value);
        if ($color) {
          return $color;
        }

        [, $name, $args] = $value;
        if ($name == "%") {
          $name = "_sprintf";
        }

        $f = $this->libFunctions[$name] ?? [$this, 'lib_' . str_replace('-', '_', $name)];

        if (is_callable($f)) {
          if ($args[0] == 'list') {
            $args = self::compressList($args[2], $args[1]);
          }

          $ret = call_user_func($f, $this->reduce($args, TRUE), $this);

          if (is_null($ret)) {
            return ["string", "", [
              $name, "(", $args, ")",
            ],
            ];
          }

          // Convert to a typed value if the result is a php primitive.
          if (is_numeric($ret)) {
            $ret = ['number', $ret, ""];
          }
          elseif (!is_array($ret)) {
            $ret = ['keyword', $ret];
          }

          return $ret;
        }

        // Plain function, reduce args.
        $value[2] = $this->reduce($value[2]);
        return $value;

      case "unary":
        [, $op, $exp] = $value;
        $exp = $this->reduce($exp);

        if ($exp[0] == "number") {
          switch ($op) {
            case "+":
              return $exp;

            case "-":
              $exp[1] *= -1;
              return $exp;
          }
        }
        return ["string", "", [$op, $exp]];
    }

    if ($forExpression) {
      switch ($value[0]) {
        case "keyword":
          if ($color = $this->coerceColor($value)) {
            return $color;
          }
          break;

        case "raw_color":
          return $this->coerceColor($value);
      }
    }

    return $value;
  }

  /**
   * Coerce a value for use in color operation.
   */
  protected function coerceColor($value) {
    switch ($value[0]) {
      case 'color':
        return $value;

      case 'raw_color':
        $c = ["color", 0, 0, 0];
        $colorStr = substr($value[1], 1);
        $num = hexdec($colorStr);
        $width = strlen($colorStr) == 3 ? 16 : 256;

        // 3 2 1
        for ($i = 3; $i > 0; $i--) {
          $t = (int) $num % $width;
          $num /= $width;

          $c[$i] = $t * (256 / $width) + $t * floor(16 / $width);
        }

        return $c;

      case 'keyword':
        $name = $value[1];
        if (isset(self::$cssColors[$name])) {
          $rgba = explode(',', self::$cssColors[$name]);

          if (isset($rgba[3])) {
            return ['color', $rgba[0], $rgba[1], $rgba[2], $rgba[3]];
          }
          return ['color', $rgba[0], $rgba[1], $rgba[2]];
        }
        return NULL;
    }
  }

  /**
   * Make something string like into a string.
   */
  protected function coerceString($value) {
    switch ($value[0]) {
      case "string":
        return $value;

      case "keyword":
        return ["string", "", [$value[1]]];
    }
    return NULL;
  }

  /**
   * Turn list of length 1 into value type.
   */
  protected function flattenList($value) {
    if ($value[0] == "list" && count($value[2]) == 1) {
      return $this->flattenList($value[2][0]);
    }
    return $value;
  }

  /**
   *
   */
  public function toBool($a) {
    return $a ? self::$TRUE : self::$FALSE;
  }

  /**
   * Evaluate an expression.
   */
  protected function evaluate($exp) {
    [, $op, $left, $right, $whiteBefore, $whiteAfter] = $exp;

    $left = $this->reduce($left, TRUE);
    $right = $this->reduce($right, TRUE);

    if ($leftColor = $this->coerceColor($left)) {
      $left = $leftColor;
    }

    if ($rightColor = $this->coerceColor($right)) {
      $right = $rightColor;
    }

    $ltype = $left[0];
    $rtype = $right[0];

    // Operators that work on all types.
    if ($op == "and") {
      return $this->toBool($left == self::$TRUE && $right == self::$TRUE);
    }

    if ($op == "=") {
      return $this->toBool($this->eq($left, $right));
    }

    if ($op == "+" && !is_null($str = $this->stringConcatenate($left, $right))) {
      return $str;
    }

    // Type based operators.
    $fname = "op_{$ltype}_{$rtype}";
    if (is_callable([$this, $fname])) {
      $out = $this->$fname($op, $left, $right);
      if (!is_null($out)) {
        return $out;
      }
    }

    // Make the expression look it did before being parsed.
    $paddedOp = $op;
    if ($whiteBefore) {
      $paddedOp = " " . $paddedOp;
    }
    if ($whiteAfter) {
      $paddedOp .= " ";
    }

    return ["string", "", [$left, $paddedOp, $right]];
  }

  /**
   *
   */
  protected function stringConcatenate($left, $right) {
    if ($strLeft = $this->coerceString($left)) {
      if ($right[0] == "string") {
        $right[1] = "";
      }
      $strLeft[2][] = $right;
      return $strLeft;
    }

    if ($strRight = $this->coerceString($right)) {
      array_unshift($strRight[2], $left);
      return $strRight;
    }
  }

  /**
   * Make sure a color's components don't go out of bounds.
   */
  protected function fixColor($c) {
    foreach (range(1, 3) as $i) {
      if ($c[$i] < 0) {
        $c[$i] = 0;
      }
      if ($c[$i] > 255) {
        $c[$i] = 255;
      }
    }

    return $c;
  }

  /**
   *
   */
  protected function op_number_color($op, $lft, $rgt) {
    if ($op == '+' || $op == '*') {
      return $this->op_color_number($op, $rgt, $lft);
    }
  }

  /**
   *
   */
  protected function op_color_number($op, $lft, $rgt) {
    if ($rgt[0] == '%') {
      $rgt[1] /= 100;
    }

    return $this->op_color_color($op, $lft,
          array_fill(1, count($lft) - 1, $rgt[1]));
  }

  /**
   *
   */
  protected function op_color_color($op, $left, $right) {
    $out = ['color'];
    $max = count($left) > count($right) ? count($left) : count($right);
    foreach (range(1, $max - 1) as $i) {
      $lval = $left[$i] ?? 0;
      $rval = $right[$i] ?? 0;
      switch ($op) {
        case '+':
          $out[] = $lval + $rval;
          break;

        case '-':
          $out[] = $lval - $rval;
          break;

        case '*':
          $out[] = $lval * $rval;
          break;

        case '%':
          $out[] = $lval % $rval;
          break;

        case '/':
          if ($rval == 0) {
            $this->throwError("evaluate error: can't divide by zero");
          }
          $out[] = $lval / $rval;
          break;

        default:
          $this->throwError('evaluate error: color op number failed on op ' . $op);
      }
    }
    return $this->fixColor($out);
  }

  /**
   *
   */
  public function lib_red($color) {
    $color = $this->coerceColor($color);
    if (is_null($color)) {
      $this->throwError('color expected for red()');
    }

    return $color[1];
  }

  /**
   *
   */
  public function lib_green($color) {
    $color = $this->coerceColor($color);
    if (is_null($color)) {
      $this->throwError('color expected for green()');
    }

    return $color[2];
  }

  /**
   *
   */
  public function lib_blue($color) {
    $color = $this->coerceColor($color);
    if (is_null($color)) {
      $this->throwError('color expected for blue()');
    }

    return $color[3];
  }

  /**
   * Operator on two numbers.
   */
  protected function op_number_number($op, $left, $right) {
    $unit = empty($left[2]) ? $right[2] : $left[2];

    $value = 0;
    switch ($op) {
      case '+':
        $value = $left[1] + $right[1];
        break;

      case '*':
        $value = $left[1] * $right[1];
        break;

      case '-':
        $value = $left[1] - $right[1];
        break;

      case '%':
        $value = $left[1] % $right[1];
        break;

      case '/':
        if ($right[1] == 0) {
          $this->throwError('parse error: divide by zero');
        }
        $value = $left[1] / $right[1];
        break;

      case '<':
        return $this->toBool($left[1] < $right[1]);

      case '>':
        return $this->toBool($left[1] > $right[1]);

      case '>=':
        return $this->toBool($left[1] >= $right[1]);

      case '=<':
        return $this->toBool($left[1] <= $right[1]);

      default:
        $this->throwError('parse error: unknown number operator: ' . $op);
    }

    return ["number", $value, $unit];
  }

  /**
   * Environment functions .
   */
  protected function makeOutputBlock($type, $selectors = NULL) {
    $b = new stdclass();
    $b->lines = [];
    $b->children = [];
    $b->selectors = $selectors;
    $b->type = $type;
    $b->parent = $this->scope;
    return $b;
  }

  /**
   * The state of execution.
   */
  protected function pushEnv($block = NULL) {
    $e = new stdclass();
    $e->parent = $this->env;
    $e->store = [];
    $e->block = $block;

    $this->env = $e;
    return $e;
  }

  /**
   * Pop something off the stack.
   */
  protected function popEnv() {
    $old = $this->env;
    $this->env = $this->env->parent;
    return $old;
  }

  /**
   * Set something in the current env.
   */
  protected function set($name, $value) {
    $this->env->store[$name] = $value;
  }

  /**
   * Get the highest occurrence entry for a name.
   */
  protected function get($name) {
    $current = $this->env;

    $isArguments = $name == $this->vPrefix . 'arguments';
    while ($current) {
      if ($isArguments && isset($current->arguments)) {
        return ['list', ' ', $current->arguments];
      }

      if (isset($current->store[$name])) {
        return $current->store[$name];
      }

      $current = $current->storeParent ??
                $current->parent;
    }

    $this->throwError("variable $name is undefined");
  }

  /**
   * Inject array of unparsed strings into environment as variables.
   */
  protected function injectVariables($args) {
    $this->pushEnv();
    $parser = new lessc_parser($this, __METHOD__);
    foreach ($args as $name => $strValue) {
      if ($name[0] !== '@') {
        $name = '@' . $name;
      }
      $parser->count = 0;
      $parser->buffer = (string) $strValue;
      if (!$parser->propertyValue($value)) {
        throw new Exception("failed to parse passed in variable $name: $strValue");
      }

      $this->set($name, $value);
    }
  }

  /**
   * Initialize any static state, can initialize parser for a file
   * $opts isn't used yet
   */
  public function __construct($fname = NULL) {
    if ($fname !== NULL) {
      // Used for deprecated parse method.
      $this->_parseFile = $fname;
    }
  }

  /**
   *
   */
  public function compile($string, $name = NULL) {
    $locale = setlocale(LC_NUMERIC, 0);
    setlocale(LC_NUMERIC, "C");

    $this->parser = $this->makeParser($name);
    $root = $this->parser->parse($string);

    $this->env = NULL;
    $this->scope = NULL;

    $this->formatter = $this->newFormatter();

    if (!empty($this->registeredVars)) {
      $this->injectVariables($this->registeredVars);
    }

    // Used for error messages.
    $this->sourceParser = $this->parser;
    $this->compileBlock($root);

    ob_start();
    $this->formatter->block($this->scope);
    $out = ob_get_clean();
    setlocale(LC_NUMERIC, $locale);
    return $out;
  }

  /**
   *
   */
  public function compileFile($fname, $outFname = NULL) {
    if (!is_readable($fname)) {
      throw new Exception('load error: failed to find ' . $fname);
    }

    $pi = pathinfo($fname);

    $oldImport = $this->importDir;

    $this->importDir = (array) $this->importDir;
    $this->importDir[] = $pi['dirname'] . '/';

    $this->addParsedFile($fname);

    $out = $this->compile(file_get_contents($fname), $fname);

    $this->importDir = $oldImport;

    if ($outFname !== NULL) {
      return file_put_contents($outFname, $out);
    }

    return $out;
  }

  /**
   * Compile only if changed input has changed or output doesn't exist.
   */
  public function checkedCompile($in, $out) {
    if (!is_file($out) || filemtime($in) > filemtime($out)) {
      $this->compileFile($in, $out);
      return TRUE;
    }
    return FALSE;
  }

  /**
   * Execute lessphp on a .less file or a lessphp cache structure.
   *
   * The lessphp cache structure contains information about a specific
   * less file having been parsed. It can be used as a hint for future
   * calls to determine whether or not a rebuild is required.
   *
   * The cache structure contains two important keys that may be used
   * externally:
   *
   * compiled: The final compiled CSS
   * updated: The time (in seconds) the CSS was last compiled
   *
   * The cache structure is a plain-ol' PHP associative array and can
   * be serialized and unserialized without a hitch.
   *
   * @param mixed $in
   *   Input.
   * @param bool $force
   *   Force rebuild?
   *
   * @return array lessphp cache structure.
   */
  public function cachedCompile($in, $force = FALSE) {
    // Assume no root.
    $root = NULL;

    if (is_string($in)) {
      $root = $in;
    }
    elseif (is_array($in) && isset($in['root'])) {
      if ($force || !isset($in['files'])) {
        // If we are forcing a recompile or if for some reason the
        // structure does not contain any file information we should
        // specify the root to trigger a rebuild.
        $root = $in['root'];
      }
      elseif (isset($in['files']) && is_array($in['files'])) {
        foreach ($in['files'] as $fname => $ftime) {
          if (!file_exists($fname) || filemtime($fname) > $ftime) {
            // One of the files we knew about previously has changed
            // so we should look at our incoming root again.
            $root = $in['root'];
            break;
          }
        }
      }
    }
    else {
      // @todo Throw an exception? We got neither a string nor something
      // that looks like a compatible lessphp cache structure.
      return NULL;
    }

    if ($root !== NULL) {
      // If we have a root value which means we should rebuild.
      $out = [];
      $out['root'] = $root;
      $out['compiled'] = $this->compileFile($root);
      $out['files'] = $this->allParsedFiles();
      $out['updated'] = time();
      return $out;
    }
    else {
      // No changes, pass back the structure
      // we were given initially.
      return $in;
    }

  }

  // Parse and compile buffer.

  /**
   * This is deprecated.
   */
  public function parse($str = NULL, $initialVariables = NULL) {
    if (is_array($str)) {
      $initialVariables = $str;
      $str = NULL;
    }

    $oldVars = $this->registeredVars;
    if ($initialVariables !== NULL) {
      $this->setVariables($initialVariables);
    }

    if ($str == NULL) {
      if (empty($this->_parseFile)) {
        throw new exception("nothing to parse");
      }

      $out = $this->compileFile($this->_parseFile);
    }
    else {
      $out = $this->compile($str);
    }

    $this->registeredVars = $oldVars;
    return $out;
  }

  /**
   *
   */
  protected function makeParser($name) {
    $parser = new lessc_parser($this, $name);
    $parser->writeComments = $this->preserveComments;

    return $parser;
  }

  /**
   *
   */
  public function setFormatter($name) {
    $this->formatterName = $name;
  }

  /**
   *
   */
  protected function newFormatter() {
    $className = "lessc_formatter_lessjs";
    if (!empty($this->formatterName)) {
      if (!is_string($this->formatterName)) {
        return $this->formatterName;
      }
      $className = "lessc_formatter_$this->formatterName";
    }

    return new $className();
  }

  /**
   *
   */
  public function setPreserveComments($preserve) {
    $this->preserveComments = $preserve;
  }

  /**
   *
   */
  public function registerFunction($name, $func) {
    $this->libFunctions[$name] = $func;
  }

  /**
   *
   */
  public function unregisterFunction($name) {
    unset($this->libFunctions[$name]);
  }

  /**
   *
   */
  public function setVariables($variables) {
    $this->registeredVars = array_merge($this->registeredVars, $variables);
  }

  /**
   *
   */
  public function unsetVariable($name) {
    unset($this->registeredVars[$name]);
  }

  /**
   *
   */
  public function setImportDir($dirs) {
    $this->importDir = (array) $dirs;
  }

  /**
   *
   */
  public function addImportDir($dir) {
    $this->importDir = (array) $this->importDir;
    $this->importDir[] = $dir;
  }

  /**
   *
   */
  public function allParsedFiles() {
    return $this->allParsedFiles;
  }

  /**
   *
   */
  public function addParsedFile($file) {
    $this->allParsedFiles[realpath($file)] = filemtime($file);
  }

  /**
   * Uses the current value of $this->count to show line and line number.
   */
  public function throwError($msg = NULL) {
    if ($this->sourceLoc >= 0) {
      $this->sourceParser->throwError($msg, $this->sourceLoc);
    }
    throw new exception($msg);
  }

  // Compile file $in to file $out if $in is newer than $out.

  /**
   * Returns true when it compiles, false otherwise.
   */
  public static function ccompile($in, $out, $less = NULL) {
    if ($less === NULL) {
      $less = new self;
    }
    return $less->checkedCompile($in, $out);
  }

  /**
   *
   */
  public static function cexecute($in, $force = FALSE, $less = NULL) {
    if ($less === NULL) {
      $less = new self;
    }
    return $less->cachedCompile($in, $force);
  }

  static protected $cssColors = [
    'aliceblue' => '240,248,255',
    'antiquewhite' => '250,235,215',
    'aqua' => '0,255,255',
    'aquamarine' => '127,255,212',
    'azure' => '240,255,255',
    'beige' => '245,245,220',
    'bisque' => '255,228,196',
    'black' => '0,0,0',
    'blanchedalmond' => '255,235,205',
    'blue' => '0,0,255',
    'blueviolet' => '138,43,226',
    'brown' => '165,42,42',
    'burlywood' => '222,184,135',
    'cadetblue' => '95,158,160',
    'chartreuse' => '127,255,0',
    'chocolate' => '210,105,30',
    'coral' => '255,127,80',
    'cornflowerblue' => '100,149,237',
    'cornsilk' => '255,248,220',
    'crimson' => '220,20,60',
    'cyan' => '0,255,255',
    'darkblue' => '0,0,139',
    'darkcyan' => '0,139,139',
    'darkgoldenrod' => '184,134,11',
    'darkgray' => '169,169,169',
    'darkgreen' => '0,100,0',
    'darkgrey' => '169,169,169',
    'darkkhaki' => '189,183,107',
    'darkmagenta' => '139,0,139',
    'darkolivegreen' => '85,107,47',
    'darkorange' => '255,140,0',
    'darkorchid' => '153,50,204',
    'darkred' => '139,0,0',
    'darksalmon' => '233,150,122',
    'darkseagreen' => '143,188,143',
    'darkslateblue' => '72,61,139',
    'darkslategray' => '47,79,79',
    'darkslategrey' => '47,79,79',
    'darkturquoise' => '0,206,209',
    'darkviolet' => '148,0,211',
    'deeppink' => '255,20,147',
    'deepskyblue' => '0,191,255',
    'dimgray' => '105,105,105',
    'dimgrey' => '105,105,105',
    'dodgerblue' => '30,144,255',
    'firebrick' => '178,34,34',
    'floralwhite' => '255,250,240',
    'forestgreen' => '34,139,34',
    'fuchsia' => '255,0,255',
    'gainsboro' => '220,220,220',
    'ghostwhite' => '248,248,255',
    'gold' => '255,215,0',
    'goldenrod' => '218,165,32',
    'gray' => '128,128,128',
    'green' => '0,128,0',
    'greenyellow' => '173,255,47',
    'grey' => '128,128,128',
    'honeydew' => '240,255,240',
    'hotpink' => '255,105,180',
    'indianred' => '205,92,92',
    'indigo' => '75,0,130',
    'ivory' => '255,255,240',
    'khaki' => '240,230,140',
    'lavender' => '230,230,250',
    'lavenderblush' => '255,240,245',
    'lawngreen' => '124,252,0',
    'lemonchiffon' => '255,250,205',
    'lightblue' => '173,216,230',
    'lightcoral' => '240,128,128',
    'lightcyan' => '224,255,255',
    'lightgoldenrodyellow' => '250,250,210',
    'lightgray' => '211,211,211',
    'lightgreen' => '144,238,144',
    'lightgrey' => '211,211,211',
    'lightpink' => '255,182,193',
    'lightsalmon' => '255,160,122',
    'lightseagreen' => '32,178,170',
    'lightskyblue' => '135,206,250',
    'lightslategray' => '119,136,153',
    'lightslategrey' => '119,136,153',
    'lightsteelblue' => '176,196,222',
    'lightyellow' => '255,255,224',
    'lime' => '0,255,0',
    'limegreen' => '50,205,50',
    'linen' => '250,240,230',
    'magenta' => '255,0,255',
    'maroon' => '128,0,0',
    'mediumaquamarine' => '102,205,170',
    'mediumblue' => '0,0,205',
    'mediumorchid' => '186,85,211',
    'mediumpurple' => '147,112,219',
    'mediumseagreen' => '60,179,113',
    'mediumslateblue' => '123,104,238',
    'mediumspringgreen' => '0,250,154',
    'mediumturquoise' => '72,209,204',
    'mediumvioletred' => '199,21,133',
    'midnightblue' => '25,25,112',
    'mintcream' => '245,255,250',
    'mistyrose' => '255,228,225',
    'moccasin' => '255,228,181',
    'navajowhite' => '255,222,173',
    'navy' => '0,0,128',
    'oldlace' => '253,245,230',
    'olive' => '128,128,0',
    'olivedrab' => '107,142,35',
    'orange' => '255,165,0',
    'orangered' => '255,69,0',
    'orchid' => '218,112,214',
    'palegoldenrod' => '238,232,170',
    'palegreen' => '152,251,152',
    'paleturquoise' => '175,238,238',
    'palevioletred' => '219,112,147',
    'papayawhip' => '255,239,213',
    'peachpuff' => '255,218,185',
    'peru' => '205,133,63',
    'pink' => '255,192,203',
    'plum' => '221,160,221',
    'powderblue' => '176,224,230',
    'purple' => '128,0,128',
    'red' => '255,0,0',
    'rosybrown' => '188,143,143',
    'royalblue' => '65,105,225',
    'saddlebrown' => '139,69,19',
    'salmon' => '250,128,114',
    'sandybrown' => '244,164,96',
    'seagreen' => '46,139,87',
    'seashell' => '255,245,238',
    'sienna' => '160,82,45',
    'silver' => '192,192,192',
    'skyblue' => '135,206,235',
    'slateblue' => '106,90,205',
    'slategray' => '112,128,144',
    'slategrey' => '112,128,144',
    'snow' => '255,250,250',
    'springgreen' => '0,255,127',
    'steelblue' => '70,130,180',
    'tan' => '210,180,140',
    'teal' => '0,128,128',
    'thistle' => '216,191,216',
    'tomato' => '255,99,71',
    'transparent' => '0,0,0,0',
    'turquoise' => '64,224,208',
    'violet' => '238,130,238',
    'wheat' => '245,222,179',
    'white' => '255,255,255',
    'whitesmoke' => '245,245,245',
    'yellow' => '255,255,0',
    'yellowgreen' => '154,205,50',
  ];

}

/**
 * Responsible for taking a string of LESS code and converting it into a
 * syntax tree.
 */
class lessc_parser {
  /**
   * Used to uniquely identify blocks.
   */
  static protected $nextBlockId = 0;

  static protected $precedence = [
    '=<' => 0,
    '>=' => 0,
    '=' => 0,
    '<' => 0,
    '>' => 0,

    '+' => 1,
    '-' => 1,
    '*' => 2,
    '/' => 2,
    '%' => 2,
  ];

  static protected $whitePattern;
  static protected $commentMulti;

  static protected $commentSingle = "//";
  static protected $commentMultiLeft = "/*";
  static protected $commentMultiRight = "*/";

  /**
   * Regex string to match any of the operators.
   */
  static protected $operatorString;

  /**
   * These properties will supress division unless it's inside parenthases.
   */
  static protected $supressDivisionProps =
        ['/border-radius$/i', '/^font$/i'];

  /**
   * @var int|mixed
   */
  public mixed $count;

  /**
   * @var mixed|string
   */
  public mixed $buffer;

  protected $blockDirectives = ["font-face", "keyframes", "page", "-moz-document", "viewport", "-moz-viewport", "-o-viewport", "-ms-viewport"];
  protected $lineDirectives = ["charset"];

  /**
   * If we are in parens we can be more liberal with whitespace around
   * operators because it must evaluate to a single value and thus is less
   * ambiguous.
   *
   * Consider:
   *     property1: 10 -5; // is two numbers, 10 and -5
   *     property2: (10 -5); // should evaluate to 5
   */
  protected $inParens = FALSE;

  /**
   * Caches preg escaped literals.
   */
  static protected $literalCache = [];

  private bool $eatWhiteDefault;
  private mixed $lessc;
  private mixed $sourceName;
  public false $writeComments;

  private int $line;

  private ?stdclass $env;

  /**
   * @var array|mixed
   */
  private mixed $seenComments;

  /**
   * @var true
   */
  private bool $inExp;

  private mixed $currentProperty;

  public function __construct($lessc, $sourceName = NULL) {
    $this->eatWhiteDefault = TRUE;
    // Reference to less needed for vPrefix, mPrefix, and parentSelector.
    $this->lessc = $lessc;

    // Name used for error messages.
    $this->sourceName = $sourceName;

    $this->writeComments = FALSE;

    if (!self::$operatorString) {
      self::$operatorString =
                '(' . implode('|', array_map(['lessc', 'preg_quote'],
                array_keys(self::$precedence))) . ')';

      $commentSingle = lessc::preg_quote(self::$commentSingle);
      $commentMultiLeft = lessc::preg_quote(self::$commentMultiLeft);
      $commentMultiRight = lessc::preg_quote(self::$commentMultiRight);

      self::$commentMulti = $commentMultiLeft . '.*?' . $commentMultiRight;
      self::$whitePattern = '/' . $commentSingle . '[^\n]*\s*|(' . self::$commentMulti . ')\s*|\s+/Ais';
    }
  }

  /**
   *
   */
  public function parse($buffer) {
    $this->count = 0;
    $this->line = 1;

    // Block stack.
    $this->env = NULL;
    $this->buffer = $this->writeComments ? $buffer : $this->removeComments($buffer);
    $this->pushSpecialBlock("root");
    $this->eatWhiteDefault = TRUE;
    $this->seenComments = [];

    // Trim whitespace on head
    // if (preg_match('/^\s+/', $this->buffer, $m)) {
    //  $this->line += substr_count($m[0], "\n");
    //  $this->buffer = ltrim($this->buffer);
    // }.
    $this->whitespace();

    // Parse the entire file.
    while (FALSE !== $this->parseChunk());

    if ($this->count != strlen($this->buffer)) {
      $this->throwError();
    }

    // @todo report where the block was opened
    if (!property_exists($this->env, 'parent') || !is_null($this->env->parent)) {
      throw new exception('parse error: unclosed block');
    }

    return $this->env;
  }

  /**
   * Parse a single chunk off the head of the buffer and append it to the
   * current parse environment.
   * Returns false when the buffer is empty, or when there is an error.
   *
   * This function is called repeatedly until the entire document is
   * parsed.
   *
   * This parser is most similar to a recursive descent parser. Single
   * functions represent discrete grammatical rules for the language, and
   * they are able to capture the text that represents those rules.
   *
   * Consider the function lessc::keyword(). (all parse functions are
   * structured the same)
   *
   * The function takes a single reference argument. When calling the
   * function it will attempt to match a keyword on the head of the buffer.
   * If it is successful, it will place the keyword in the referenced
   * argument, advance the position in the buffer, and return true. If it
   * fails then it won't advance the buffer and it will return false.
   *
   * All of these parse functions are powered by lessc::match(), which behaves
   * the same way, but takes a literal regular expression. Sometimes it is
   * more convenient to use match instead of creating a new function.
   *
   * Because of the format of the functions, to parse an entire string of
   * grammatical rules, you can chain them together using &&.
   *
   * But, if some of the rules in the chain succeed before one fails, then
   * the buffer position will be left at an invalid state. In order to
   * avoid this, lessc::seek() is used to remember and set buffer positions.
   *
   * Before parsing a chain, use $s = $this->seek() to remember the current
   * position into $s. Then if a chain fails, use $this->seek($s) to
   * go back where we started.
   */
  protected function parseChunk() {
    if (empty($this->buffer)) {
      return FALSE;
    }
    $s = $this->seek();

    if ($this->whitespace()) {
      return TRUE;
    }

    // Setting a property.
    if ($this->keyword($key) && $this->assign() &&
          $this->propertyValue($value, $key) && $this->end()
      ) {
      $this->append(['assign', $key, $value], $s);
      return TRUE;
    }
    else {
      $this->seek($s);
    }

    // Look for special css blocks.
    if ($this->literal('@', FALSE)) {
      $this->count--;

      // Media.
      if ($this->literal('@media')) {
        if (($this->mediaQueryList($mediaQueries) || TRUE)
              && $this->literal('{')
          ) {
          $media = $this->pushSpecialBlock("media");
          $media->queries = is_null($mediaQueries) ? [] : $mediaQueries;
          return TRUE;
        }
        else {
          $this->seek($s);
          return FALSE;
        }
      }

      if ($this->literal("@", FALSE) && $this->keyword($dirName)) {
        if ($this->isDirective($dirName, $this->blockDirectives)) {
          if (($this->openString("{", $dirValue, NULL, [";"]) || TRUE) &&
                $this->literal("{")
            ) {
            $dir = $this->pushSpecialBlock("directive");
            $dir->name = $dirName;
            if (isset($dirValue)) {
              $dir->value = $dirValue;
            }
            return TRUE;
          }
        }
        elseif ($this->isDirective($dirName, $this->lineDirectives)) {
          if ($this->propertyValue($dirValue) && $this->end()) {
            $this->append(["directive", $dirName, $dirValue]);
            return TRUE;
          }
        }
      }

      $this->seek($s);
    }

    // Setting a variable.
    if ($this->variable($var) && $this->assign() &&
          $this->propertyValue($value) && $this->end()
      ) {
      $this->append(['assign', $var, $value], $s);
      return TRUE;
    }
    else {
      $this->seek($s);
    }

    if ($this->import($importValue)) {
      $this->append($importValue, $s);
      return TRUE;
    }

    // Opening parametric mixin.
    if ($this->tag($tag, TRUE) && $this->argumentDef($args, $isVararg) &&
          ($this->guards($guards) || TRUE) &&
          $this->literal('{')
      ) {
      $block = $this->pushBlock($this->fixTags([$tag]));
      $block->args = $args;
      $block->isVararg = $isVararg;
      if (!empty($guards)) {
        $block->guards = $guards;
      }
      return TRUE;
    }
    else {
      $this->seek($s);
    }

    // Opening a simple block.
    if ($this->tags($tags) && $this->literal('{', FALSE)) {
      $tags = $this->fixTags($tags);
      $this->pushBlock($tags);
      return TRUE;
    }
    else {
      $this->seek($s);
    }

    // Closing a block.
    if ($this->literal('}', FALSE)) {
      try {
        $block = $this->pop();
      }
      catch (exception $e) {
        $this->seek($s);
        $this->throwError($e->getMessage());
      }

      $hidden = FALSE;
      if (is_null($block->type)) {
        $hidden = TRUE;
        if (!isset($block->args)) {
          foreach ($block->tags as $tag) {
            if (!is_string($tag) || $tag[0] != $this->lessc->mPrefix) {
              $hidden = FALSE;
              break;
            }
          }
        }

        foreach ($block->tags as $tag) {
          if (is_string($tag)) {
            $this->env->children[$tag][] = $block;
          }
        }
      }

      if (!$hidden) {
        $this->append(['block', $block], $s);
      }

      // This is done here so comments aren't bundled into he block that
      // was just closed.
      $this->whitespace();
      return TRUE;
    }

    // Mixin.
    if ($this->mixinTags($tags) &&
          ($this->argumentDef($argv, $isVararg) || TRUE) &&
          ($this->keyword($suffix) || TRUE) && $this->end()
      ) {
      $tags = $this->fixTags($tags);
      $this->append(['mixin', $tags, $argv, $suffix], $s);
      return TRUE;
    }
    else {
      $this->seek($s);
    }

    // Spare ;.
    if ($this->literal(';')) {
      return TRUE;
    }

    // Got nothing, throw error.
    return FALSE;
  }

  /**
   *
   */
  protected function isDirective($dirname, $directives) {
    // @todo cache pattern in parser
    $pattern = implode("|",
          array_map(["lessc", "preg_quote"], $directives));
    $pattern = '/^(-[a-z-]+-)?(' . $pattern . ')$/i';

    return preg_match($pattern, $dirname);
  }

  /**
   *
   */
  protected function fixTags($tags) {
    // Move @ tags out of variable namespace.
    foreach ($tags as &$tag) {
      if ($tag[0] == $this->lessc->vPrefix) {
        $tag[0] = $this->lessc->mPrefix;
      }
    }
    return $tags;
  }

  /**
   * A list of expressions.
   */
  protected function expressionList(&$exps) {
    $values = [];

    while ($this->expression($exp)) {
      $values[] = $exp;
    }

    if (count($values) == 0) {
      return FALSE;
    }

    $exps = lessc::compressList($values, ' ');
    return TRUE;
  }

  /**
   * Attempt to consume an expression.
   * @link http://en.wikipedia.org/wiki/Operator-precedence_parser#Pseudo-code
   */
  protected function expression(&$out) {
    if ($this->value($lhs)) {
      $out = $this->expHelper($lhs, 0);

      // Look for / shorthand.
      if (!empty($this->env->supressedDivision)) {
        unset($this->env->supressedDivision);
        $s = $this->seek();
        if ($this->literal("/") && $this->value($rhs)) {
          $out = ["list", "",
                [$out, ["keyword", "/"], $rhs],
          ];
        }
        else {
          $this->seek($s);
        }
      }

      return TRUE;
    }
    return FALSE;
  }

  /**
   * Recursively parse infix equation with $lhs at precedence $minP.
   */
  protected function expHelper($lhs, $minP) {
    $this->inExp = TRUE;
    $ss = $this->seek();

    while (TRUE) {
      $whiteBefore = isset($this->buffer[$this->count - 1]) &&
                ctype_space($this->buffer[$this->count - 1]);

      // If there is whitespace before the operator, then we require
      // whitespace after the operator for it to be an expression.
      $needWhite = $whiteBefore && !$this->inParens;

      if ($this->match(self::$operatorString . ($needWhite ? '\s' : ''), $m) && self::$precedence[$m[1]] >= $minP) {
        if (!$this->inParens && isset($this->env->currentProperty) && $m[1] == "/" && empty($this->env->supressedDivision)) {
          foreach (self::$supressDivisionProps as $pattern) {
            if (preg_match($pattern, $this->env->currentProperty)) {
              $this->env->supressedDivision = TRUE;
              break 2;
            }
          }
        }

        $whiteAfter = isset($this->buffer[$this->count - 1]) &&
                    ctype_space($this->buffer[$this->count - 1]);

        if (!$this->value($rhs)) {
          break;
        }

        // Peek for next operator to see what to do with rhs.
        if ($this->peek(self::$operatorString, $next) && self::$precedence[$next[1]] > self::$precedence[$m[1]]) {
          $rhs = $this->expHelper($rhs, self::$precedence[$next[1]]);
        }

        $lhs = ['expression', $m[1], $lhs, $rhs, $whiteBefore, $whiteAfter];
        $ss = $this->seek();

        continue;
      }

      break;
    }

    $this->seek($ss);

    return $lhs;
  }

  /**
   * Consume a list of values for a property.
   */
  public function propertyValue(&$value, $keyName = NULL) {
    $values = [];

    if ($keyName !== NULL) {
      $this->env->currentProperty = $keyName;
    }

    $s = NULL;
    while ($this->expressionList($v)) {
      $values[] = $v;
      $s = $this->seek();
      if (!$this->literal(',')) {
        break;
      }
    }

    if ($s) {
      $this->seek($s);
    }

    if ($keyName !== NULL) {
      unset($this->env->currentProperty);
    }

    if (count($values) == 0) {
      return FALSE;
    }

    $value = lessc::compressList($values, ', ');
    return TRUE;
  }

  /**
   *
   */
  protected function parenValue(&$out) {
    $s = $this->seek();

    // Speed shortcut.
    if (isset($this->buffer[$this->count]) && $this->buffer[$this->count] != "(") {
      return FALSE;
    }

    $inParens = $this->inParens;
    if ($this->literal("(") &&
          ($this->inParens = TRUE) && $this->expression($exp) &&
          $this->literal(")")
      ) {
      $out = $exp;
      $this->inParens = $inParens;
      return TRUE;
    }
    else {
      $this->inParens = $inParens;
      $this->seek($s);
    }

    return FALSE;
  }

  /**
   * A single value.
   */
  protected function value(&$value) {
    $s = $this->seek();

    // Speed shortcut.
    if (isset($this->buffer[$this->count]) && $this->buffer[$this->count] == "-") {
      // Negation.
      if ($this->literal("-", FALSE) &&
            (($this->variable($inner) && $inner = ["variable", $inner]) ||
            $this->unit($inner) ||
            $this->parenValue($inner))
        ) {
        $value = ["unary", "-", $inner];
        return TRUE;
      }
      else {
        $this->seek($s);
      }
    }

    if ($this->parenValue($value)) {
      return TRUE;
    }
    if ($this->unit($value)) {
      return TRUE;
    }
    if ($this->color($value)) {
      return TRUE;
    }
    if ($this->func($value)) {
      return TRUE;
    }
    if ($this->string($value)) {
      return TRUE;
    }

    if ($this->keyword($word)) {
      $value = ['keyword', $word];
      return TRUE;
    }

    // Try a variable.
    if ($this->variable($var)) {
      $value = ['variable', $var];
      return TRUE;
    }

    // Unquote string (should this work on any type?
    if ($this->literal("~") && $this->string($str)) {
      $value = ["escape", $str];
      return TRUE;
    }
    else {
      $this->seek($s);
    }

    // Css hack: \0.
    if ($this->literal('\\') && $this->match('([0-9]+)', $m)) {
      $value = ['keyword', '\\' . $m[1]];
      return TRUE;
    }
    else {
      $this->seek($s);
    }

    return FALSE;
  }

  /**
   * An import statement.
   */
  protected function import(&$out) {
    if (!$this->literal('@import')) {
      return FALSE;
    }

    // @import "something.css" media;
    // @import url("something.css") media;
    // @import url(something.css) media;
    if ($this->propertyValue($value)) {
      $out = ["import", $value];
      return TRUE;
    }
  }

  /**
   *
   */
  protected function mediaQueryList(&$out) {
    if ($this->genericList($list, "mediaQuery", ",", FALSE)) {
      $out = $list[2];
      return TRUE;
    }
    return FALSE;
  }

  /**
   *
   */
  protected function mediaQuery(&$out) {
    $s = $this->seek();

    $expressions = NULL;
    $parts = [];

    if (($this->literal("only") && ($only = TRUE) || $this->literal("not") && ($not = TRUE) || TRUE) && $this->keyword($mediaType)) {
      $prop = ["mediaType"];
      if (isset($only)) {
        $prop[] = "only";
      }
      if (isset($not)) {
        $prop[] = "not";
      }
      $prop[] = $mediaType;
      $parts[] = $prop;
    }
    else {
      $this->seek($s);
    }

    if (!empty($mediaType) && !$this->literal("and")) {
      // ~
    }
    else {
      $this->genericList($expressions, "mediaExpression", "and", FALSE);
      if (is_array($expressions)) {
        $parts = array_merge($parts, $expressions[2]);
      }
    }

    if (count($parts) == 0) {
      $this->seek($s);
      return FALSE;
    }

    $out = $parts;
    return TRUE;
  }

  /**
   *
   */
  protected function mediaExpression(&$out) {
    $s = $this->seek();
    $value = NULL;
    if ($this->literal("(") &&
          $this->keyword($feature) &&
          ($this->literal(":") && $this->expression($value) || TRUE) &&
          $this->literal(")")
      ) {
      $out = ["mediaExp", $feature];
      if ($value) {
        $out[] = $value;
      }
      return TRUE;
    }
    elseif ($this->variable($variable)) {
      $out = ['variable', $variable];
      return TRUE;
    }

    $this->seek($s);
    return FALSE;
  }

  /**
   * An unbounded string stopped by $end.
   */
  protected function openString($end, &$out, $nestingOpen = NULL, $rejectStrs = NULL) {
    $oldWhite = $this->eatWhiteDefault;
    $this->eatWhiteDefault = FALSE;

    $stop = ["'", '"', "@{", $end];
    $stop = array_map(["lessc", "preg_quote"], $stop);
    // $stop[] = self::$commentMulti;
    if (!is_null($rejectStrs)) {
      $stop = array_merge($stop, $rejectStrs);
    }

    $patt = '(.*?)(' . implode("|", $stop) . ')';

    $nestingLevel = 0;

    $content = [];
    while ($this->match($patt, $m, FALSE)) {
      if (!empty($m[1])) {
        $content[] = $m[1];
        if ($nestingOpen) {
          $nestingLevel += substr_count($m[1], $nestingOpen);
        }
      }

      $tok = $m[2];

      $this->count -= strlen($tok);
      if ($tok == $end) {
        if ($nestingLevel == 0) {
          break;
        }
        else {
          $nestingLevel--;
        }
      }

      if (($tok == "'" || $tok == '"') && $this->string($str)) {
        $content[] = $str;
        continue;
      }

      if ($tok == "@{" && $this->interpolation($inter)) {
        $content[] = $inter;
        continue;
      }

      if (!empty($rejectStrs) && in_array($tok, $rejectStrs)) {
        break;
      }

      $content[] = $tok;
      $this->count += strlen($tok);
    }

    $this->eatWhiteDefault = $oldWhite;

    if (count($content) == 0) {
      return FALSE;
    }

    // Trim the end.
    if (is_string(end($content))) {
      $content[count($content) - 1] = rtrim(end($content));
    }

    $out = ["string", "", $content];
    return TRUE;
  }

  /**
   *
   */
  protected function string(&$out) {
    $s = $this->seek();
    if ($this->literal('"', FALSE)) {
      $delim = '"';
    }
    elseif ($this->literal("'", FALSE)) {
      $delim = "'";
    }
    else {
      return FALSE;
    }

    $content = [];

    // Look for either ending delim , escape, or string interpolation.
    $patt = '([^\n]*?)(@\{|\\\\|' .
            lessc::preg_quote($delim) . ')';

    $oldWhite = $this->eatWhiteDefault;
    $this->eatWhiteDefault = FALSE;

    while ($this->match($patt, $m, FALSE)) {
      $content[] = $m[1];
      if ($m[2] == "@{") {
        $this->count -= strlen($m[2]);
        if ($this->interpolation($inter, FALSE)) {
          $content[] = $inter;
        }
        else {
          $this->count += strlen($m[2]);
          // Ignore it.
          $content[] = "@{";
        }
      }
      elseif ($m[2] == '\\') {
        $content[] = $m[2];
        if ($this->literal($delim, FALSE)) {
          $content[] = $delim;
        }
      }
      else {
        $this->count -= strlen($delim);
        // Delim.
        break;
      }
    }

    $this->eatWhiteDefault = $oldWhite;

    if ($this->literal($delim)) {
      $out = ["string", $delim, $content];
      return TRUE;
    }

    $this->seek($s);
    return FALSE;
  }

  /**
   *
   */
  protected function interpolation(&$out) {
    $oldWhite = $this->eatWhiteDefault;
    $this->eatWhiteDefault = TRUE;

    $s = $this->seek();
    if ($this->literal("@{") &&
          $this->openString("}", $interp, NULL, ["'", '"', ";"]) &&
          $this->literal("}", FALSE)
      ) {
      $out = ["interpolate", $interp];
      $this->eatWhiteDefault = $oldWhite;
      if ($this->eatWhiteDefault) {
        $this->whitespace();
      }
      return TRUE;
    }

    $this->eatWhiteDefault = $oldWhite;
    $this->seek($s);
    return FALSE;
  }

  /**
   *
   */
  protected function unit(&$unit) {
    // Speed shortcut.
    if (isset($this->buffer[$this->count])) {
      $char = $this->buffer[$this->count];
      if (!ctype_digit($char) && $char != ".") {
        return FALSE;
      }
    }

    if ($this->match('([0-9]+(?:\.[0-9]*)?|\.[0-9]+)([%a-zA-Z]+)?', $m)) {
      $unit = ["number", $m[1], empty($m[2]) ? "" : $m[2]];
      return TRUE;
    }
    return FALSE;
  }

  /**
   * A # color.
   */
  protected function color(&$out) {
    if ($this->match('(#(?:[0-9a-f]{8}|[0-9a-f]{6}|[0-9a-f]{3}))', $m)) {
      if (strlen($m[1]) > 7) {
        $out = ["string", "", [$m[1]]];
      }
      else {
        $out = ["raw_color", $m[1]];
      }
      return TRUE;
    }

    return FALSE;
  }

  // Consume an argument definition list surrounded by ()
  // each argument is a variable name with optional value
  // or at the end a ... or a variable named followed by ...
  // arguments are separated by , unless a ; is in the list, then ; is the.

  /**
   * Delimiter.
   */
  protected function argumentDef(&$args, &$isVararg) {
    $s = $this->seek();
    if (!$this->literal('(')) {
      return FALSE;
    }

    $values = [];
    $delim = ",";
    $method = "expressionList";

    $isVararg = FALSE;
    while (TRUE) {
      if ($this->literal("...")) {
        $isVararg = TRUE;
        break;
      }

      if ($this->$method($value)) {
        if ($value[0] == "variable") {
          $arg = ["arg", $value[1]];
          $ss = $this->seek();

          if ($this->assign() && $this->$method($rhs)) {
            $arg[] = $rhs;
          }
          else {
            $this->seek($ss);
            if ($this->literal("...")) {
              $arg[0] = "rest";
              $isVararg = TRUE;
            }
          }

          $values[] = $arg;
          if ($isVararg) {
            break;
          }
          continue;
        }
        else {
          $values[] = ["lit", $value];
        }
      }

      if (!$this->literal($delim)) {
        if ($delim == "," && $this->literal(";")) {
          // Found new delim, convert existing args.
          $delim = ";";
          $method = "propertyValue";

          // Transform arg list.
          // 2 items.
          if (isset($values[1])) {
            $newList = [];
            foreach ($values as $i => $arg) {
              switch ($arg[0]) {
                case "arg":
                  if ($i) {
                    $this->throwError("Cannot mix ; and , as delimiter types");
                  }
                  $newList[] = $arg[2];
                  break;

                case "lit":
                  $newList[] = $arg[1];
                  break;

                case "rest":
                  $this->throwError("Unexpected rest before semicolon");
              }
            }

            $newList = ["list", ", ", $newList];

            switch ($values[0][0]) {
              case "arg":
                $newArg = ["arg", $values[0][1], $newList];
                break;

              case "lit":
                $newArg = ["lit", $newList];
                break;
            }

            // 1 item
          }
          elseif ($values) {
            $newArg = $values[0];
          }

          if ($newArg) {
            $values = [$newArg];
          }
        }
        else {
          break;
        }
      }
    }

    if (!$this->literal(')')) {
      $this->seek($s);
      return FALSE;
    }

    $args = $values;

    return TRUE;
  }

  // Consume a list of tags.

  /**
   * This accepts a hanging delimiter.
   */
  protected function tags(&$tags, $simple = FALSE, $delim = ',') {
    $tags = [];
    while ($this->tag($tt, $simple)) {
      $tags[] = $tt;
      if (!$this->literal($delim)) {
        break;
      }
    }
    if (count($tags) == 0) {
      return FALSE;
    }

    return TRUE;
  }

  // List of tags of specifying mixin path.

  /**
   * Optionally separated by > (lazy, accepts extra >)
   */
  protected function mixinTags(&$tags) {
    $tags = [];
    while ($this->tag($tt, TRUE)) {
      $tags[] = $tt;
      $this->literal(">");
    }

    if (!$tags) {
      return FALSE;
    }

    return TRUE;
  }

  /**
   * A bracketed value (contained within in a tag definition)
   */
  protected function tagBracket(&$parts, &$hasExpression) {
    // Speed shortcut.
    if (isset($this->buffer[$this->count]) && $this->buffer[$this->count] != "[") {
      return FALSE;
    }

    $s = $this->seek();

    $hasInterpolation = FALSE;

    if ($this->literal("[", FALSE)) {
      $attrParts = ["["];
      // keyword, string, operator.
      while (TRUE) {
        if ($this->literal("]", FALSE)) {
          $this->count--;
          // Get out early.
          break;
        }

        if ($this->match('\s+', $m)) {
          $attrParts[] = " ";
          continue;
        }
        if ($this->string($str)) {
          // Escape parent selector, (yuck)
          foreach ($str[2] as &$chunk) {
            $chunk = str_replace($this->lessc->parentSelector, "$&$", $chunk);
          }

          $attrParts[] = $str;
          $hasInterpolation = TRUE;
          continue;
        }

        if ($this->keyword($word)) {
          $attrParts[] = $word;
          continue;
        }

        if ($this->interpolation($inter, FALSE)) {
          $attrParts[] = $inter;
          $hasInterpolation = TRUE;
          continue;
        }

        // operator, handles attr namespace too.
        if ($this->match('[|-~\$\*\^=]+', $m)) {
          $attrParts[] = $m[0];
          continue;
        }

        break;
      }

      if ($this->literal("]", FALSE)) {
        $attrParts[] = "]";
        foreach ($attrParts as $part) {
          $parts[] = $part;
        }
        $hasExpression = $hasExpression || $hasInterpolation;
        return TRUE;
      }
      $this->seek($s);
    }

    $this->seek($s);
    return FALSE;
  }

  /**
   * A space separated list of selectors.
   */
  protected function tag(&$tag, $simple = FALSE) {
    if ($simple) {
      $chars = '^@,:;{}\][>\(\) "\'';
    }
    else {
      $chars = '^@,;{}["\'';
    }
    $s = $this->seek();

    $hasExpression = FALSE;
    $parts = [];
    while ($this->tagBracket($parts, $hasExpression));

    $oldWhite = $this->eatWhiteDefault;
    $this->eatWhiteDefault = FALSE;

    while (TRUE) {
      if ($this->match('([' . $chars . '0-9][' . $chars . ']*)', $m)) {
        $parts[] = $m[1];
        if ($simple) {
          break;
        }

        while ($this->tagBracket($parts, $hasExpression));
        continue;
      }

      if (isset($this->buffer[$this->count]) && $this->buffer[$this->count] == "@") {
        if ($this->interpolation($interp)) {
          $hasExpression = TRUE;
          // don't unescape.
          $interp[2] = TRUE;
          $parts[] = $interp;
          continue;
        }

        if ($this->literal("@")) {
          $parts[] = "@";
          continue;
        }
      }

      // For keyframes.
      if ($this->unit($unit)) {
        $parts[] = $unit[1];
        $parts[] = $unit[2];
        continue;
      }

      break;
    }

    $this->eatWhiteDefault = $oldWhite;
    if (!$parts) {
      $this->seek($s);
      return FALSE;
    }

    if ($hasExpression) {
      $tag = ["exp", ["string", "", $parts]];
    }
    else {
      $tag = trim(implode($parts));
    }

    $this->whitespace();
    return TRUE;
  }

  /**
   * A css function.
   */
  protected function func(&$func) {
    $s = $this->seek();

    if ($this->match('(%|[\w\-_][\w\-_:\.]+|[\w_])', $m) && $this->literal('(')) {
      $fname = $m[1];

      $sPreArgs = $this->seek();

      $args = [];
      while (TRUE) {
        $ss = $this->seek();
        // This ugly nonsense is for ie filter properties.
        if ($this->keyword($name) && $this->literal('=') && $this->expressionList($value)) {
          $args[] = ["string", "", [$name, "=", $value]];
        }
        else {
          $this->seek($ss);
          if ($this->expressionList($value)) {
            $args[] = $value;
          }
        }

        if (!$this->literal(',')) {
          break;
        }
      }
      $args = ['list', ',', $args];

      if ($this->literal(')')) {
        $func = ['function', $fname, $args];
        return TRUE;
      }
      elseif ($fname == 'url') {
        // couldn't parse and in url? treat as string.
        $this->seek($sPreArgs);
        if ($this->openString(")", $string) && $this->literal(")")) {
          $func = ['function', $fname, $string];
          return TRUE;
        }
      }
    }

    $this->seek($s);
    return FALSE;
  }

  /**
   * Consume a less variable.
   */
  protected function variable(&$name) {
    $s = $this->seek();
    if ($this->literal($this->lessc->vPrefix, FALSE) &&
          ($this->variable($sub) || $this->keyword($name))
      ) {
      if (!empty($sub)) {
        $name = ['variable', $sub];
      }
      else {
        $name = $this->lessc->vPrefix . $name;
      }
      return TRUE;
    }

    $name = NULL;
    $this->seek($s);
    return FALSE;
  }

  /**
   * Consume an assignment operator
   * Can optionally take a name that will be set to the current property name
   */
  protected function assign($name = NULL) {
    if ($name) {
      $this->currentProperty = $name;
    }
    return $this->literal(':') || $this->literal('=');
  }

  /**
   * Consume a keyword.
   */
  protected function keyword(&$word) {
    if ($this->match('([\w_\-\*!"][\w\-_"]*)', $m)) {
      $word = $m[1];
      return TRUE;
    }
    return FALSE;
  }

  /**
   * Consume an end of statement delimiter.
   */
  protected function end() {
    if ($this->literal(';', FALSE)) {
      return TRUE;
    }
    elseif ($this->count == strlen($this->buffer) || $this->buffer[$this->count] == '}') {
      // If there is end of file or a closing block next then we don't need a ;.
      return TRUE;
    }
    return FALSE;
  }

  /**
   *
   */
  protected function guards(&$guards) {
    $s = $this->seek();

    if (!$this->literal("when")) {
      $this->seek($s);
      return FALSE;
    }

    $guards = [];

    while ($this->guardGroup($g)) {
      $guards[] = $g;
      if (!$this->literal(",")) {
        break;
      }
    }

    if (count($guards) == 0) {
      $guards = NULL;
      $this->seek($s);
      return FALSE;
    }

    return TRUE;
  }

  // A bunch of guards that are and'd together.

  /**
   * @todo rename to guardGroup.
   */
  protected function guardGroup(&$guardGroup) {
    $s = $this->seek();
    $guardGroup = [];
    while ($this->guard($guard)) {
      $guardGroup[] = $guard;
      if (!$this->literal("and")) {
        break;
      }
    }

    if (count($guardGroup) == 0) {
      $guardGroup = NULL;
      $this->seek($s);
      return FALSE;
    }

    return TRUE;
  }

  /**
   *
   */
  protected function guard(&$guard) {
    $s = $this->seek();
    $negate = $this->literal("not");

    if ($this->literal("(") && $this->expression($exp) && $this->literal(")")) {
      $guard = $exp;
      if ($negate) {
        $guard = ["negate", $guard];
      }
      return TRUE;
    }

    $this->seek($s);
    return FALSE;
  }

  /**
   * Raw parsing functions .
   */
  protected function literal($what, $eatWhitespace = NULL) {
    if ($eatWhitespace === NULL) {
      $eatWhitespace = $this->eatWhiteDefault;
    }

    // Shortcut on single letter.
    if (!isset($what[1]) && isset($this->buffer[$this->count])) {
      if ($this->buffer[$this->count] == $what) {
        if (!$eatWhitespace) {
          $this->count++;
          return TRUE;
        }
        // Goes below...
      }
      else {
        return FALSE;
      }
    }

    if (!isset(self::$literalCache[$what])) {
      self::$literalCache[$what] = lessc::preg_quote($what);
    }

    return $this->match(self::$literalCache[$what], $m, $eatWhitespace);
  }

  /**
   *
   */
  protected function genericList(&$out, $parseItem, $delim = "", $flatten = TRUE) {
    $s = $this->seek();
    $items = [];
    while ($this->$parseItem($value)) {
      $items[] = $value;
      if ($delim) {
        if (!$this->literal($delim)) {
          break;
        }
      }
    }

    if (count($items) == 0) {
      $this->seek($s);
      return FALSE;
    }

    if ($flatten && count($items) == 1) {
      $out = $items[0];
    }
    else {
      $out = ["list", $delim, $items];
    }

    return TRUE;
  }

  // Advance counter to next occurrence of $what
  // $until - don't include $what in advance.

  /**
   * $allowNewline, if string, will be used as valid char set.
   */
  protected function to($what, &$out, $until = FALSE, $allowNewline = FALSE) {
    if (is_string($allowNewline)) {
      $validChars = $allowNewline;
    }
    else {
      $validChars = $allowNewline ? "." : "[^\n]";
    }
    if (!$this->match('(' . $validChars . '*?)' . lessc::preg_quote($what), $m, !$until)) {
      return FALSE;
    }
    // Give back $what.
    if ($until) {
      $this->count -= strlen($what);
    }
    $out = $m[1];
    return TRUE;
  }

  /**
   * Try to match something on head of buffer.
   */
  protected function match($regex, &$out, $eatWhitespace = NULL) {
    if ($eatWhitespace === NULL) {
      $eatWhitespace = $this->eatWhiteDefault;
    }

    $r = '/' . $regex . ($eatWhitespace && !$this->writeComments ? '\s*' : '') . '/Ais';
    if (preg_match($r, $this->buffer, $out, PREG_UNMATCHED_AS_NULL, $this->count)) {
      $this->count += strlen($out[0]);
      if ($eatWhitespace && $this->writeComments) {
        $this->whitespace();
      }
      return TRUE;
    }
    return FALSE;
  }

  /**
   * Match some whitespace.
   */
  protected function whitespace() {
    if ($this->writeComments) {
      $gotWhite = FALSE;
      while (preg_match(self::$whitePattern, $this->buffer, $m, PREG_UNMATCHED_AS_NULL, $this->count)) {
        if (isset($m[1]) && empty($this->seenComments[$this->count])) {
          $this->append(["comment", $m[1]]);
          $this->seenComments[$this->count] = TRUE;
        }
        $this->count += strlen($m[0]);
        $gotWhite = TRUE;
      }
      return $gotWhite;
    }
    else {
      $this->match("", $m);
      return strlen($m[0]) > 0;
    }
  }

  /**
   * Match something without consuming it.
   */
  protected function peek($regex, &$out = NULL, $from = NULL) {
    if (is_null($from)) {
      $from = $this->count;
    }
    $r = '/' . $regex . '/Ais';
    $result = preg_match($r, $this->buffer, $out, PREG_UNMATCHED_AS_NULL, $from);

    return $result;
  }

  /**
   * Seek to a spot in the buffer or return where we are on no argument.
   */
  protected function seek($where = NULL) {
    if ($where === NULL) {
      return $this->count;
    }
    else {
      $this->count = $where;
    }
    return TRUE;
  }

  /**
   * Misc functions .
   */
  public function throwError($msg = "parse error", $count = NULL) {
    $count = is_null($count) ? $this->count : $count;

    $line = $this->line +
            substr_count(substr($this->buffer, 0, $count), "\n");

    if (!empty($this->sourceName)) {
      $loc = "$this->sourceName on line $line";
    }
    else {
      $loc = "line: $line";
    }

    // @todo this depends on $this->count
    if ($this->peek("(.*?)(\n|$)", $m, $count)) {
      throw new exception("$msg: failed at `$m[1]` $loc");
    }
    else {
      throw new exception("$msg: $loc");
    }
  }

  /**
   *
   */
  protected function pushBlock($selectors = NULL, $type = NULL) {
    $b = new stdclass();
    $b->parent = $this->env;

    $b->type = $type;
    $b->id = self::$nextBlockId++;

    // @todo kill me from here
    $b->isVararg = FALSE;
    $b->tags = $selectors;

    $b->props = [];
    $b->children = [];

    $this->env = $b;
    return $b;
  }

  /**
   * Push a block that doesn't multiply tags.
   */
  protected function pushSpecialBlock($type) {
    return $this->pushBlock(NULL, $type);
  }

  /**
   * Append a property to the current block.
   */
  protected function append($prop, $pos = NULL) {
    if ($pos !== NULL) {
      $prop[-1] = $pos;
    }
    $this->env->props[] = $prop;
  }

  /**
   * Pop something off the stack.
   */
  protected function pop() {
    $old = $this->env;
    $this->env = $this->env->parent;
    return $old;
  }

  // Remove comments from $text.

  /**
   * @todo make it work for all functions, not just url.
   */
  protected function removeComments($text) {
    $look = [
      'url(', '//', '/*', '"', "'",
    ];

    $out = '';
    $min = NULL;
    while (TRUE) {
      // Find the next item.
      foreach ($look as $token) {
        $pos = strpos($text, $token);
        if ($pos !== FALSE) {
          if (!isset($min) || $pos < $min[1]) {
            $min = [$token, $pos];
          }
        }
      }

      if (is_null($min)) {
        break;
      }

      $count = $min[1];
      $skip = 0;
      $newlines = 0;
      switch ($min[0]) {
        case 'url(':
          if (preg_match('/url\(.*?\)/', $text, $m, PREG_UNMATCHED_AS_NULL, $count)) {
            $count += strlen($m[0]) - strlen($min[0]);
          }
          break;

        case '"':
        case "'":
          if (preg_match('/' . $min[0] . '.*?(?<!\\\\)' . $min[0] . '/', $text, $m, PREG_UNMATCHED_AS_NULL, $count)) {
            $count += strlen($m[0]) - 1;
          }
          break;

        case '//':
          $skip = strpos($text, "\n", $count);
          if ($skip === FALSE) {
            $skip = strlen($text) - $count;
          }
          else {
            $skip -= $count;
          }
          break;

        case '/*':
          if (preg_match('/\/\*.*?\*\//s', $text, $m, PREG_UNMATCHED_AS_NULL, $count)) {
            $skip = strlen($m[0]);
            $newlines = substr_count($m[0], "\n");
          }
          break;
      }

      if ($skip == 0) {
        $count += strlen($min[0]);
      }

      $out .= substr($text, 0, $count) . str_repeat("\n", $newlines);
      $text = substr($text, $count + $skip);

      $min = NULL;
    }

    return $out . $text;
  }

}

/**
 *
 */
class lessc_formatter_classic {
  public $indentChar = "  ";

  public $break = "\n";
  public $open = " {";
  public $close = "}";
  public $selectorSeparator = ", ";
  public $assignSeparator = ":";

  public $openSingle = " { ";
  public $closeSingle = " }";

  public $disableSingle = FALSE;
  public $breakSelectors = FALSE;

  public $compressColors = FALSE;

  private int $indentLevel;

  public function __construct() {
    $this->indentLevel = 0;
  }

  /**
   *
   */
  public function indentStr($n = 0) {
    return str_repeat($this->indentChar, max($this->indentLevel + $n, 0));
  }

  /**
   *
   */
  public function property($name, $value) {
    return $name . $this->assignSeparator . $value . ";";
  }

  /**
   *
   */
  protected function isEmpty($block) {
    if (empty($block->lines)) {
      foreach ($block->children as $child) {
        if (!$this->isEmpty($child)) {
          return FALSE;
        }
      }

      return TRUE;
    }
    return FALSE;
  }

  /**
   *
   */
  public function block($block) {
    if ($this->isEmpty($block)) {
      return;
    }

    $inner = $pre = $this->indentStr();

    $isSingle = !$this->disableSingle &&
            is_null($block->type) && count($block->lines) == 1;

    if (!empty($block->selectors)) {
      $this->indentLevel++;

      if ($this->breakSelectors) {
        $selectorSeparator = $this->selectorSeparator . $this->break . $pre;
      }
      else {
        $selectorSeparator = $this->selectorSeparator;
      }

      echo $pre .
                implode($selectorSeparator, $block->selectors);
      if ($isSingle) {
        echo $this->openSingle;
        $inner = "";
      }
      else {
        echo $this->open . $this->break;
        $inner = $this->indentStr();
      }

    }

    if (!empty($block->lines)) {
      $glue = $this->break . $inner;
      echo $inner . implode($glue, $block->lines);
      if (!$isSingle && !empty($block->children)) {
        echo $this->break;
      }
    }

    foreach ($block->children as $child) {
      $this->block($child);
    }

    if (!empty($block->selectors)) {
      if (!$isSingle && empty($block->children)) {
        echo $this->break;
      }

      if ($isSingle) {
        echo $this->closeSingle . $this->break;
      }
      else {
        echo $pre . $this->close . $this->break;
      }

      $this->indentLevel--;
    }
  }

}

/**
 *
 */
class lessc_formatter_compressed extends lessc_formatter_classic {
  public $disableSingle = TRUE;
  public $open = "{";
  public $selectorSeparator = ",";
  public $assignSeparator = ":";
  public $break = "";
  public $compressColors = TRUE;

  /**
   *
   */
  public function indentStr($n = 0) {
    return "";
  }

}

/**
 *
 */
class lessc_formatter_lessjs extends lessc_formatter_classic {
  public $disableSingle = TRUE;
  public $breakSelectors = TRUE;
  public $assignSeparator = ": ";
  public $selectorSeparator = ",";

}
