import Blockly from ".."

class nlGenerator extends Blockly.CodeGenerator {

    variable(block:Blockly.Block) {
        return [block.getFieldValue('NAME'),0]
    }

    quantifier(block:Blockly.Block) {
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

}

export default new nlGenerator("natural_language")