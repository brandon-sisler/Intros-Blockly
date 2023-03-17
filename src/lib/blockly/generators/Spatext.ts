import Blockly from ".."

class SpatextGenerator extends Blockly.CodeGenerator {
    _outputType = (block:Blockly.Block|null):"math"|"language"|null => {
        if (block === null) {
            return null
        } else if (block.type === "quantifier") {
            return "language"
        } else if ( block.type === "negation") {
            return this._outputType(block.getInputTargetBlock("PROPOSITION"))
        } else {
            return "math"
        }
    }

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
        if (this._outputType(block.getInputTargetBlock("PREDICATE")) === "math") {
            result = result + "<m>" + this.valueToCode(block, 'PREDICATE', 0) + "</m>";
        } else {
            result = result + this.valueToCode(block, 'PREDICATE', 0);
        }
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
        if (this._outputType(block.getInputTargetBlock("PROPOSITION")) === "math") {
            result = "\\neg "+this.valueToCode(block, 'PROPOSITION', 0);
        } else {
            result = 'it is false that ' + this.valueToCode(block, 'PROPOSITION', 0);
        }
        return [result, 0]
    }

    theorem = (block:Blockly.Block) => {
        let prop = this.valueToCode(block, 'PROPOSITION', 0);
        prop = prop.trim();
        let result = '<knowl mode="theorem">\n';
        result = result + '    <title>' + block.getFieldValue('NAME') + '</title>\n'
        result = result + '    <content>\n';
        result = result + '        <p>' + prop.charAt(0).toUpperCase() + prop.slice(1) + '.</p>\n';
        result = result + '    </content>\n';
        result = result + '    <outtro>\n';
        result = result + this.statementToCode(block, 'ARGUMENT') + "\n";
        result = result + '    </outtro>\n';
        result = result + '</knowl>';
        return result
    }

    intro = (block:Blockly.Block) => {
        return "<p>Let <m>" + block.getFieldValue("NAME") + "</m> be a proposition.</p>"
    }
        
    exact= (block:Blockly.Block) => {
        return 'Exactly TODO lol'
    }
    
    destruct = (block:Blockly.Block) => {
        let result = `<p>From <m>${this.valueToCode(block, 'ASSUMPTIONPROP', 0)}</m> `;
        result = result + `we have both <m>${this.valueToCode(block, 'PROPOSITION1', 0)}</m> and <m>${this.valueToCode(block, 'PROPOSITION2', 0)}</m>.</p>`
        return result
    }
    
    conj = (block:Blockly.Block) => {
        return `<p>From both <m>${block.getFieldValue('HYPOTHESIS1')}</m> and `+
            `<m>${block.getFieldValue('HYPOTHESIS2')}</m> we have <m>...</m>.`;
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
