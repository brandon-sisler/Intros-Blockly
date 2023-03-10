import Blockly from 'blockly'
import combination from './blocks/combination';
import conj from './blocks/conj';
import destruct from './blocks/destruct';
import intro from './blocks/intro';
import negation from './blocks/negation';
import quantifier from './blocks/quantifier';
import theorem from './blocks/theorem';
import variable from './blocks/variable';
import exact from './blocks/exact';

Blockly.common.defineBlocksWithJsonArray([
    combination,
    conj,
    destruct,
    intro,
    negation,
    quantifier,
    theorem,
    variable,
    exact
]);

export default Blockly

export function createWorkspace(div:HTMLElement,opts:Blockly.BlocklyOptions) {
    const workspace = Blockly.inject(div,opts);
    const startBlock = workspace.newBlock("theorem");
    startBlock.setDeletable(false);
    startBlock.setMovable(false);
    startBlock.initSvg();
    workspace.render();
    workspace.addChangeListener(Blockly.Events.disableOrphans);
    return workspace
  }