import {Proposition} from '../utils'

export default {
  "type": "quantifier",
  "message0": "%1 %2 %3",
  "args0": [
    {
      "type": "field_dropdown",
      "name": "TYPE",
      "options": [
        [
          "∀",
          "forall"
        ],
        [
          "∃",
          "exists"
        ]
      ]
    },
    {
      "type": "input_value",
      "name": "VARIABLE",
      "check": "Variable"
    },
    {
      "type": "input_value",
      "name": "PREDICATE",
      "check": Proposition
    }
  ],
  "inputsInline": false,
  "output": "Formula",
  "colour": 180,
}