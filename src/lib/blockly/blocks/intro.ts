import {Proposition} from '../types'

export default {
  "type": "intro",
  "message0": "Let %1 be the %2 %3",
  "args0": [
    {
      "type": "field_input",
      "name": "NAME",
      "text": "P"
    },
    {
      "type": "field_dropdown",
      "name": "TYPE",
      "options": [
        [
          "proposition",
          "forall"
        ],
        [
          "assumption that",
          "implies"
        ]
      ]
    },
    {
      "type": "input_value",
      "name": "PROPOSITION",
      "check": Proposition,
    }
  ],
  "colour": 150,
  "previousStatement": null,
  "nextStatement": null,
}