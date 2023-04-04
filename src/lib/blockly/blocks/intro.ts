import {Proposition} from '../types'

export default {
  "type": "intro",
  "message0": "Let %1 be a proposition",
  "args0": [
    {
      "type": "input_value",
      "name": "PROPOSITION",
      "check": Proposition,
    }
  ],
  "colour": 270,
  "previousStatement": null,
  "nextStatement": null,
}