%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:56 EST 2020

% Result     : Theorem 1.14s
% Output     : CNFRefutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   26 (  40 expanded)
%              Number of clauses        :   19 (  20 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   81 ( 167 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t26_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_3,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,X2)
       => r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X3)) ) ),
    inference(assume_negation,[status(cth)],[t26_xboole_1])).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_8,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k3_xboole_0(esk3_0,esk5_0),k3_xboole_0(esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2)
    | r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_13])).

cnf(c_0_21,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))
    | ~ r2_hidden(esk1_2(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk1_2(k3_xboole_0(esk3_0,X1),X2),esk4_0)
    | r1_tarski(k3_xboole_0(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(esk3_0,esk5_0),k3_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:16:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.14/1.33  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 1.14/1.33  # and selection function SelectVGNonCR.
% 1.14/1.33  #
% 1.14/1.33  # Preprocessing time       : 0.026 s
% 1.14/1.33  # Presaturation interreduction done
% 1.14/1.33  
% 1.14/1.33  # Proof found!
% 1.14/1.33  # SZS status Theorem
% 1.14/1.33  # SZS output start CNFRefutation
% 1.14/1.33  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.14/1.33  fof(t26_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_xboole_1)).
% 1.14/1.33  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.14/1.33  fof(c_0_3, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 1.14/1.33  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X3)))), inference(assume_negation,[status(cth)],[t26_xboole_1])).
% 1.14/1.33  fof(c_0_5, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.14/1.33  cnf(c_0_6, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 1.14/1.33  cnf(c_0_7, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 1.14/1.33  fof(c_0_8, negated_conjecture, (r1_tarski(esk3_0,esk4_0)&~r1_tarski(k3_xboole_0(esk3_0,esk5_0),k3_xboole_0(esk4_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 1.14/1.33  cnf(c_0_9, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 1.14/1.33  cnf(c_0_10, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 1.14/1.33  cnf(c_0_11, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_6])).
% 1.14/1.33  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_7])).
% 1.14/1.33  cnf(c_0_13, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 1.14/1.33  cnf(c_0_14, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 1.14/1.33  cnf(c_0_15, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.14/1.33  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_9])).
% 1.14/1.33  cnf(c_0_17, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X3)|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 1.14/1.33  cnf(c_0_18, plain, (r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2)|r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 1.14/1.33  cnf(c_0_19, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 1.14/1.33  cnf(c_0_20, plain, (r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X1)|r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_16, c_0_13])).
% 1.14/1.33  cnf(c_0_21, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))|~r2_hidden(esk1_2(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)),X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 1.14/1.33  cnf(c_0_22, negated_conjecture, (r2_hidden(esk1_2(k3_xboole_0(esk3_0,X1),X2),esk4_0)|r1_tarski(k3_xboole_0(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 1.14/1.33  cnf(c_0_23, negated_conjecture, (~r1_tarski(k3_xboole_0(esk3_0,esk5_0),k3_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.14/1.33  cnf(c_0_24, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 1.14/1.33  cnf(c_0_25, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24])]), ['proof']).
% 1.14/1.33  # SZS output end CNFRefutation
% 1.14/1.33  # Proof object total steps             : 26
% 1.14/1.33  # Proof object clause steps            : 19
% 1.14/1.33  # Proof object formula steps           : 7
% 1.14/1.33  # Proof object conjectures             : 9
% 1.14/1.33  # Proof object clause conjectures      : 6
% 1.14/1.33  # Proof object formula conjectures     : 3
% 1.14/1.33  # Proof object initial clauses used    : 8
% 1.14/1.33  # Proof object initial formulas used   : 3
% 1.14/1.33  # Proof object generating inferences   : 10
% 1.14/1.33  # Proof object simplifying inferences  : 2
% 1.14/1.33  # Training examples: 0 positive, 0 negative
% 1.14/1.33  # Parsed axioms                        : 3
% 1.14/1.33  # Removed by relevancy pruning/SinE    : 0
% 1.14/1.33  # Initial clauses                      : 11
% 1.14/1.33  # Removed in clause preprocessing      : 0
% 1.14/1.33  # Initial clauses in saturation        : 11
% 1.14/1.33  # Processed clauses                    : 7561
% 1.14/1.33  # ...of these trivial                  : 2268
% 1.14/1.33  # ...subsumed                          : 4299
% 1.14/1.33  # ...remaining for further processing  : 994
% 1.14/1.33  # Other redundant clauses eliminated   : 3
% 1.14/1.33  # Clauses deleted for lack of memory   : 0
% 1.14/1.33  # Backward-subsumed                    : 3
% 1.14/1.33  # Backward-rewritten                   : 17
% 1.14/1.33  # Generated clauses                    : 153897
% 1.14/1.33  # ...of the previous two non-trivial   : 123593
% 1.14/1.33  # Contextual simplify-reflections      : 5
% 1.14/1.33  # Paramodulations                      : 153404
% 1.14/1.33  # Factorizations                       : 460
% 1.14/1.33  # Equation resolutions                 : 33
% 1.14/1.33  # Propositional unsat checks           : 0
% 1.14/1.33  #    Propositional check models        : 0
% 1.14/1.33  #    Propositional check unsatisfiable : 0
% 1.14/1.33  #    Propositional clauses             : 0
% 1.14/1.33  #    Propositional clauses after purity: 0
% 1.14/1.33  #    Propositional unsat core size     : 0
% 1.14/1.33  #    Propositional preprocessing time  : 0.000
% 1.14/1.33  #    Propositional encoding time       : 0.000
% 1.14/1.33  #    Propositional solver time         : 0.000
% 1.14/1.33  #    Success case prop preproc time    : 0.000
% 1.14/1.33  #    Success case prop encoding time   : 0.000
% 1.14/1.33  #    Success case prop solver time     : 0.000
% 1.14/1.33  # Current number of processed clauses  : 963
% 1.14/1.33  #    Positive orientable unit clauses  : 276
% 1.14/1.33  #    Positive unorientable unit clauses: 0
% 1.14/1.33  #    Negative unit clauses             : 0
% 1.14/1.33  #    Non-unit-clauses                  : 687
% 1.14/1.33  # Current number of unprocessed clauses: 116050
% 1.14/1.33  # ...number of literals in the above   : 276954
% 1.14/1.33  # Current number of archived formulas  : 0
% 1.14/1.33  # Current number of archived clauses   : 31
% 1.14/1.33  # Clause-clause subsumption calls (NU) : 147853
% 1.14/1.33  # Rec. Clause-clause subsumption calls : 107426
% 1.14/1.33  # Non-unit clause-clause subsumptions  : 4307
% 1.14/1.33  # Unit Clause-clause subsumption calls : 12516
% 1.14/1.33  # Rewrite failures with RHS unbound    : 0
% 1.14/1.33  # BW rewrite match attempts            : 8103
% 1.14/1.33  # BW rewrite match successes           : 17
% 1.14/1.33  # Condensation attempts                : 0
% 1.14/1.33  # Condensation successes               : 0
% 1.14/1.33  # Termbank termtop insertions          : 2391488
% 1.14/1.34  
% 1.14/1.34  # -------------------------------------------------
% 1.14/1.34  # User time                : 0.927 s
% 1.14/1.34  # System time              : 0.056 s
% 1.14/1.34  # Total time               : 0.983 s
% 1.14/1.34  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
