import Blockly from ".."
import { formulas } from "../utils"

class SpatextGenerator extends Blockly.CodeGenerator {
    variable = (block:Blockly.Block) => {
        return [block.getFieldValue('NAME'),0]
    }

    quantifier = (block:Blockly.Block) => {
        let type = block.getFieldValue('TYPE');
        let result = "for all propositions "
        if (type !== "forall") {
            result = "there exists a proposition "
        }
        result = result + '<m>' + this.valueToCode(block, 'VARIABLE', 0) + '</m>';
        if (type === "forall") {
            result = result + ', '
        } else {
            result = result + ' such that '
        }
        result = result + this.valueToCode(block, 'PREDICATE', 0);
        return [result, 0]
    }

    combination = (block:Blockly.Block) => {
        let result = this.valueToCode(block, 'PROPOSITION1', 0);
        let type = block.getFieldValue('TYPE');
        if (type=="and") {
            result = result + " \\wedge ";
        } else if (type=="implies") {
            result = result + " \\rightarrow ";
        } else if (type=="iff") {
            result = result + " \\leftrightarrow ";
        } else {
            result = result + " \\vee ";
        }
        result = result + this.valueToCode(block, 'PROPOSITION2', 0);
        return [result, 0]
    }

    negation = (block:Blockly.Block) => {
        let result:string
        if (!block.getInputTargetBlock("PROPOSITION")) {
            result = "<m>\\neg</m>";
        } else if (formulas.includes(block.getInputTargetBlock("PROPOSITION")!.type)) {
            result = "not "+this.valueToCode(block, 'PROPOSITION', 0);
        } else {
            result = '<m>\\neg ' + this.valueToCode(block, 'PROPOSITION', 0) + '</m>';
        }
        return [result, 0]
    }

    theorem = (block:Blockly.Block) => {
        let prop = this.valueToCode(block, 'PROPOSITION', 0);
        prop = prop.trim();
        let result = '<knowl mode="theorem">\n';
        result = result + '  <title>' + block.getFieldValue('NAME') + '</title>\n'
        result = result + '  <content>\n';
        result = result + '    <p>' + prop.charAt(0).toUpperCase() + prop.slice(1) + '.</p>\n';
        result = result + '  </content>\n';
        result = result + '  <outtro>\n';
        result = result + this.statementToCode(block, 'ARGUMENT') + "\n";
        result = result + '  </outtro>\n';
        result = result + '</knowl>';
        return result
    }

    intro = (block:Blockly.Block) => {
        // var parent = block.getSurroundParent()
        // if (parent) {
        //   var prop = parent.getInputTargetBlock("PROPOSITION")
        //   if (prop) {
        //     return prop.nlIntro(block.getFieldValue("NAME"))
        //   }
        // }
        return "<p>Let <m>" + block.getFieldValue("NAME") + "</m> be a proposition.</p>"
    }
    
    destruct = (block:Blockly.Block) => {
        let result = `<p>From <m>${this.valueToCode(block, 'ASSUMPTIONPROP', 0)}</m> `;
        result = result + `we have both <m>${this.valueToCode(block, 'PROPOSITION1', 0)}</m> and <m>${this.valueToCode(block, 'PROPOSITION2', 0)}</m>.</p>`
        return result
    }
    
    scrub_ = (block:Blockly.Block,code:string,thisOnly:boolean) => {
        const nextBlock = block.nextConnection && block.nextConnection.targetBlock();
        if (nextBlock && !thisOnly) {
            return code + '\n' + this.blockToCode(nextBlock);
        }
        return code;
    }

    INDENT = " ".repeat(4)
}

export default new SpatextGenerator("SpaTeXt")
