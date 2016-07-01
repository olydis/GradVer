import { EditStatement } from "./EditStatement";
import { EditVerificationFormula } from "./EditVerificationFormula";

export class EditInstructions
{
    private statements: EditStatement[];
    private verificationFormulas: EditVerificationFormula[];

    public get numInstructions(): number
    {
        return this.statements.length;
    }

    public constructor(
        private container: JQuery
    )
    {
        this.statements = [];
        this.verificationFormulas = [];
        this.verificationFormulas.push(new EditVerificationFormula());
        this.insertInstruction(0);
    }

    private removeInstruction(index: number): void
    {
        this.verificationFormulas.splice(index, 1);
        this.statements.splice(index, 1);
        this.updateGUI();
    }

    private insertInstruction(index: number): void
    {
        this.verificationFormulas.splice(index, 0, new EditVerificationFormula());
        this.statements.splice(index, 0, new EditStatement());
        this.updateGUI();
    }

    private updateGUI(): void
    {
        var createRightButton = (s: string) =>
            $("<span>")
                .addClass("rightFloat")
                .append($("<span>")
                    .addClass("button")
                    .addClass("buttonAutohide")
                    .text(s));

        this.container.text("");
        var n = this.numInstructions;
        for (var i = 0; i <= n; ++i)
            ((i: number) =>
            {
                this.container.append(createRightButton("+").click(() => this.insertInstruction(i)));
                this.container.append(createRightButton("⇳").click(() => {}));
                // this.container.append(createRightButton("↲").click(() => {}));
                // this.container.append(createRightButton("↰").click(() => {}));
                this.container.append(this.verificationFormulas[i].createHTML());
                if (i != n)
                {
                    this.container.append(createRightButton("-").click(() => this.removeInstruction(i)));
                    this.container.append(createRightButton("✓").click(() => {}));
                    this.container.append(this.statements[i].createHTML());
                }
            })(i);
    }
}