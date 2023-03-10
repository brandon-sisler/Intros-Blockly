import Blockly from ".."
import { snake_case } from "../../utils";

class CoqGenerator extends Blockly.CodeGenerator {
    variable = (block:Blockly.Block) => {
        return [block.getFieldValue('NAME'), 0];
    }

    quantifier = (block:Blockly.Block) => {
        var pred = this.valueToCode(block, 'PREDICATE', 0);
        let result = block.getFieldValue('TYPE') + ' ' + this.valueToCode(block, 'VARIABLE', 0) + ' : Prop, ' + pred
        return [result, 0]
    }

    combination = (block:Blockly.Block) => {
        let connection:string = ""
        var type = block.getFieldValue('TYPE');
        if (type == 'and') {
            connection = '/\\';
        } else if (type == 'or') {
            connection = '\\/';
        } else if (type == 'implies') {
            connection = '->';
        } else if (type == 'iff') {
            connection = '<->';
        }
        var result = this.valueToCode(block, 'PROPOSITION1', 0) + ' ' + connection + ' ' + this.valueToCode(block, 'PROPOSITION2', 0);
        return [result, 0]
    }

    negation = (block:Blockly.Block) => {
        var result = "~ " + this.valueToCode(block, 'PROPOSITION', 0);
        return [result, 0]
    }

    theorem = (block:Blockly.Block) => {
        return "Theorem " + snake_case(block.getFieldValue('NAME')) + " : " +
          this.valueToCode(block, 'PROPOSITION', 0).trim() + ".\n" +
          "Proof.\n" +
          this.statementToCode(block, 'ARGUMENT') +
          "\nQed.\n"
    }

    intro = (block:Blockly.Block) => {
        return 'intro ' + block.getFieldValue('NAME') +".";
    }
        
    exact= (block:Blockly.Block) => {
        return 'exact ' + block.getFieldValue('NAME') +".";
    }
    
    destruct = (block:Blockly.Block) => {
        return `destruct ${block.getFieldValue('ASSUMPTION')} (${block.getFieldValue('HYPOTHESIS1')},${block.getFieldValue('HYPOTHESIS2')}).`;
      
    }
    scrub_ = (block:Blockly.Block,code:string,thisOnly:boolean) => {
        const nextBlock =
            block.nextConnection && block.nextConnection.targetBlock();
        if (nextBlock && !thisOnly) {
          return code + '\n' + this.blockToCode(nextBlock);
        }
        return code;
    }

    INDENT = " ".repeat(0)
}

export default new CoqGenerator("Coq")
