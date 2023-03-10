

const coqGenerator = new Blockly.Generator('coq');




coqGenerator['variable'] = function (block) {
  return [block.getFieldValue('NAME'), 0];
}





coqGenerator['quantifier'] = function (block) {
  var pred = coqGenerator.valueToCode(block, 'PREDICATE', 0);
  let result = block.getFieldValue('TYPE') + ' ' + coqGenerator.valueToCode(block, 'VARIABLE', 0) + ' : Prop, ' + pred
  return [result, 0]
}




coqGenerator['combination'] = function (block) {
  var type = block.getFieldValue('TYPE');
  if (type == 'and') {
    var connection = '/\\';
  } else if (type == 'or') {
    var connection = '\\/';
  } else if (type == 'implies') {
    var connection = '->';
  } else if (type == 'iff') {
    var connection = '<->';
  }
  var result = coqGenerator.valueToCode(block, 'PROPOSITION1', 0) + ' ' + connection + ' ' + coqGenerator.valueToCode(block, 'PROPOSITION2', 0);
  return [result, 0]
}




coqGenerator['negation'] = function (block) {
  var result = "~ " + coqGenerator.valueToCode(block, 'PROPOSITION', 0);
  return [result, 0]
}

// // TODO
// Blockly.Extensions.registerMixin('quantifierMixin', {
//   nlIntro: function(p) {
//       return "<p>Let <m>" + p + "</m> be a proposition.</p>"
//   }
// });
// Blockly.Extensions.registerMixin('combinationMixin', {
//   nlIntro: function(h) {
//       return "<p>Let <m>" + h + "</m> be the assumpton that " + nlGenerator.valueToCode(this, 'PROPOSITION1' ,0) + ".</p>"
//   }
// });




coqGenerator['theorem'] = function (block) {
  return "Theorem " + snake_case(block.getFieldValue('NAME')) + " : " +
    coqGenerator.valueToCode(block, 'PROPOSITION', 0).trim() + ".\n" +
    "Proof.\n" +
    coqGenerator.statementToCode(block, 'ARGUMENT')
}





coqGenerator['intro'] = function (block) {
  return 'intro ' + block.getFieldValue('NAME') +".";
}




coqGenerator['destruct'] = function (block) {
  return `destruct ${block.getFieldValue('ASSUMPTION')} (${block.getFieldValue('HYPOTHESIS1')},${block.getFieldValue('HYPOTHESIS2')}).`;
}





coqGenerator.scrub_  = function(block, code, thisOnly) {
  const nextBlock =
      block.nextConnection && block.nextConnection.targetBlock();
  if (nextBlock && !thisOnly) {
    return code + '\n' + coqGenerator.blockToCode(nextBlock);
  }
  return code;
};
coqGenerator.INDENT = " ".repeat(0)







export function coqOutput(workspace) {
  return coqGenerator.workspaceToCode(workspace);
}