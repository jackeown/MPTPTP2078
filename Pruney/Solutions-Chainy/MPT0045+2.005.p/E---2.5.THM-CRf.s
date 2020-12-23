%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:03 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   27 (  57 expanded)
%              Number of clauses        :   18 (  26 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   79 ( 223 expanded)
%              Number of equality atoms :   21 (  56 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t38_xboole_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,k4_xboole_0(X2,X1))
       => X1 = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t38_xboole_1])).

fof(c_0_6,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_7,plain,(
    ! [X20,X21] :
      ( ( k4_xboole_0(X20,X21) != k1_xboole_0
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | k4_xboole_0(X20,X21) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_8,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_10,negated_conjecture,
    ( r1_tarski(esk3_0,k4_xboole_0(esk4_0,esk3_0))
    & esk3_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_11,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk3_0,k4_xboole_0(esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,k4_xboole_0(esk4_0,esk3_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(X1,X1,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk3_0,esk3_0),k4_xboole_0(esk4_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk2_3(esk3_0,esk3_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_17]),c_0_18]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n011.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 11:23:12 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.35  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.17/0.35  # and selection function SelectNewComplexAHP.
% 0.17/0.35  #
% 0.17/0.35  # Preprocessing time       : 0.027 s
% 0.17/0.35  
% 0.17/0.35  # Proof found!
% 0.17/0.35  # SZS status Theorem
% 0.17/0.35  # SZS output start CNFRefutation
% 0.17/0.35  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.17/0.35  fof(t38_xboole_1, conjecture, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 0.17/0.35  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.17/0.35  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.17/0.35  fof(c_0_4, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.17/0.35  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t38_xboole_1])).
% 0.17/0.35  fof(c_0_6, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.17/0.35  fof(c_0_7, plain, ![X20, X21]:((k4_xboole_0(X20,X21)!=k1_xboole_0|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|k4_xboole_0(X20,X21)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.17/0.35  cnf(c_0_8, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.17/0.35  cnf(c_0_9, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.17/0.35  fof(c_0_10, negated_conjecture, (r1_tarski(esk3_0,k4_xboole_0(esk4_0,esk3_0))&esk3_0!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.17/0.35  cnf(c_0_11, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.17/0.35  cnf(c_0_12, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.35  cnf(c_0_13, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.17/0.35  cnf(c_0_14, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.17/0.35  cnf(c_0_15, negated_conjecture, (r1_tarski(esk3_0,k4_xboole_0(esk4_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.35  cnf(c_0_16, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.17/0.35  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_11])).
% 0.17/0.35  cnf(c_0_18, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.17/0.35  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.17/0.35  cnf(c_0_20, negated_conjecture, (r2_hidden(X1,k4_xboole_0(esk4_0,esk3_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.17/0.35  cnf(c_0_21, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(X1,X1,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.17/0.35  cnf(c_0_22, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.35  cnf(c_0_23, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_19])).
% 0.17/0.35  cnf(c_0_24, negated_conjecture, (r2_hidden(esk2_3(esk3_0,esk3_0,esk3_0),k4_xboole_0(esk4_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.17/0.35  cnf(c_0_25, negated_conjecture, (~r2_hidden(esk2_3(esk3_0,esk3_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.17/0.35  cnf(c_0_26, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_17]), c_0_18]), c_0_22]), ['proof']).
% 0.17/0.35  # SZS output end CNFRefutation
% 0.17/0.35  # Proof object total steps             : 27
% 0.17/0.35  # Proof object clause steps            : 18
% 0.17/0.35  # Proof object formula steps           : 9
% 0.17/0.35  # Proof object conjectures             : 9
% 0.17/0.35  # Proof object clause conjectures      : 6
% 0.17/0.35  # Proof object formula conjectures     : 3
% 0.17/0.35  # Proof object initial clauses used    : 9
% 0.17/0.35  # Proof object initial formulas used   : 4
% 0.17/0.35  # Proof object generating inferences   : 9
% 0.17/0.35  # Proof object simplifying inferences  : 4
% 0.17/0.35  # Training examples: 0 positive, 0 negative
% 0.17/0.35  # Parsed axioms                        : 5
% 0.17/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.35  # Initial clauses                      : 14
% 0.17/0.35  # Removed in clause preprocessing      : 0
% 0.17/0.35  # Initial clauses in saturation        : 14
% 0.17/0.35  # Processed clauses                    : 57
% 0.17/0.35  # ...of these trivial                  : 2
% 0.17/0.35  # ...subsumed                          : 20
% 0.17/0.35  # ...remaining for further processing  : 35
% 0.17/0.35  # Other redundant clauses eliminated   : 0
% 0.17/0.35  # Clauses deleted for lack of memory   : 0
% 0.17/0.35  # Backward-subsumed                    : 1
% 0.17/0.35  # Backward-rewritten                   : 0
% 0.17/0.35  # Generated clauses                    : 106
% 0.17/0.35  # ...of the previous two non-trivial   : 77
% 0.17/0.35  # Contextual simplify-reflections      : 2
% 0.17/0.35  # Paramodulations                      : 99
% 0.17/0.35  # Factorizations                       : 2
% 0.17/0.35  # Equation resolutions                 : 5
% 0.17/0.35  # Propositional unsat checks           : 0
% 0.17/0.35  #    Propositional check models        : 0
% 0.17/0.35  #    Propositional check unsatisfiable : 0
% 0.17/0.35  #    Propositional clauses             : 0
% 0.17/0.35  #    Propositional clauses after purity: 0
% 0.17/0.35  #    Propositional unsat core size     : 0
% 0.17/0.35  #    Propositional preprocessing time  : 0.000
% 0.17/0.35  #    Propositional encoding time       : 0.000
% 0.17/0.35  #    Propositional solver time         : 0.000
% 0.17/0.35  #    Success case prop preproc time    : 0.000
% 0.17/0.35  #    Success case prop encoding time   : 0.000
% 0.17/0.35  #    Success case prop solver time     : 0.000
% 0.17/0.35  # Current number of processed clauses  : 34
% 0.17/0.35  #    Positive orientable unit clauses  : 9
% 0.17/0.35  #    Positive unorientable unit clauses: 0
% 0.17/0.35  #    Negative unit clauses             : 3
% 0.17/0.35  #    Non-unit-clauses                  : 22
% 0.17/0.35  # Current number of unprocessed clauses: 34
% 0.17/0.35  # ...number of literals in the above   : 87
% 0.17/0.35  # Current number of archived formulas  : 0
% 0.17/0.35  # Current number of archived clauses   : 1
% 0.17/0.35  # Clause-clause subsumption calls (NU) : 57
% 0.17/0.35  # Rec. Clause-clause subsumption calls : 48
% 0.17/0.35  # Non-unit clause-clause subsumptions  : 16
% 0.17/0.35  # Unit Clause-clause subsumption calls : 5
% 0.17/0.35  # Rewrite failures with RHS unbound    : 0
% 0.17/0.35  # BW rewrite match attempts            : 9
% 0.17/0.35  # BW rewrite match successes           : 0
% 0.17/0.35  # Condensation attempts                : 0
% 0.17/0.35  # Condensation successes               : 0
% 0.17/0.35  # Termbank termtop insertions          : 1804
% 0.17/0.35  
% 0.17/0.35  # -------------------------------------------------
% 0.17/0.35  # User time                : 0.027 s
% 0.17/0.35  # System time              : 0.006 s
% 0.17/0.35  # Total time               : 0.033 s
% 0.17/0.35  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
