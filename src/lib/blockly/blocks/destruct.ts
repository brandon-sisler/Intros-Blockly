import {Proposition} from '../types'

export default {
  "type": "destruct",
  "message0": "From %1 %2 we have both %3 %4 and %5 %6",
  "args0": [
    {
      "type": "field_input",
      "name": "ASSUMPTION",
      "text": "H"
    },
    {
      "type": "input_value",
      "name": "ASSUMPTIONPROP",
      // "check": "combination",
    },
    {
      "type": "field_input",
      "name": "HYPOTHESIS1",
      "text": "HP"
    },
    {
      "type": "input_value",
      "name": "PROPOSITION1",
      "check": Proposition,
    },
    {
      "type": "field_input",
      "name": "HYPOTHESIS2",
      "text": "HQ"
    },
    {
      "type": "input_value",
      "name": "PROPOSITION2",
      "check": Proposition,
    }
  ],
  "inputsInline": true,
  "colour": 90,
  "previousStatement": null,
  "nextStatement": null,
}