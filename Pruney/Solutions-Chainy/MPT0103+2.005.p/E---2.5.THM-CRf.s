%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:06 EST 2020

% Result     : Theorem 0.87s
% Output     : CNFRefutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :   29 (  36 expanded)
%              Number of clauses        :   16 (  17 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 109 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t96_xboole_1,conjecture,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

fof(c_0_6,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_8,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X19,X20] : r1_tarski(k4_xboole_0(X19,X20),X19) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_10,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_xboole_0(X13,X14) )
      & ( r2_hidden(esk2_2(X13,X14),X14)
        | r1_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_11,plain,(
    ! [X21,X22] : r1_xboole_0(k4_xboole_0(X21,X22),X22) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_12,plain,(
    ! [X10,X11,X12] :
      ( ( ~ r2_hidden(X10,X11)
        | ~ r2_hidden(X10,X12)
        | ~ r2_hidden(X10,k5_xboole_0(X11,X12)) )
      & ( r2_hidden(X10,X11)
        | r2_hidden(X10,X12)
        | ~ r2_hidden(X10,k5_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X10,X11)
        | r2_hidden(X10,X12)
        | r2_hidden(X10,k5_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X10,X12)
        | r2_hidden(X10,X11)
        | r2_hidden(X10,k5_xboole_0(X11,X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_14,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t96_xboole_1])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),k5_xboole_0(X1,X4))
    | r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X4)
    | r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_23,negated_conjecture,(
    ~ r1_tarski(k4_xboole_0(esk3_0,esk4_0),k5_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_24,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_8])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),k5_xboole_0(X1,X3)),X3)
    | r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk3_0,esk4_0),k5_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:08:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.87/1.05  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S04EN
% 0.87/1.05  # and selection function PSelectNewComplex.
% 0.87/1.05  #
% 0.87/1.05  # Preprocessing time       : 0.027 s
% 0.87/1.05  # Presaturation interreduction done
% 0.87/1.05  
% 0.87/1.05  # Proof found!
% 0.87/1.05  # SZS status Theorem
% 0.87/1.05  # SZS output start CNFRefutation
% 0.87/1.05  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.87/1.05  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.87/1.05  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.87/1.05  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.87/1.05  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.87/1.05  fof(t96_xboole_1, conjecture, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_xboole_1)).
% 0.87/1.05  fof(c_0_6, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.87/1.05  cnf(c_0_7, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.87/1.05  cnf(c_0_8, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.87/1.05  fof(c_0_9, plain, ![X19, X20]:r1_tarski(k4_xboole_0(X19,X20),X19), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.87/1.05  fof(c_0_10, plain, ![X13, X14, X16, X17, X18]:(((r2_hidden(esk2_2(X13,X14),X13)|r1_xboole_0(X13,X14))&(r2_hidden(esk2_2(X13,X14),X14)|r1_xboole_0(X13,X14)))&(~r2_hidden(X18,X16)|~r2_hidden(X18,X17)|~r1_xboole_0(X16,X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.87/1.05  fof(c_0_11, plain, ![X21, X22]:r1_xboole_0(k4_xboole_0(X21,X22),X22), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.87/1.05  fof(c_0_12, plain, ![X10, X11, X12]:(((~r2_hidden(X10,X11)|~r2_hidden(X10,X12)|~r2_hidden(X10,k5_xboole_0(X11,X12)))&(r2_hidden(X10,X11)|r2_hidden(X10,X12)|~r2_hidden(X10,k5_xboole_0(X11,X12))))&((~r2_hidden(X10,X11)|r2_hidden(X10,X12)|r2_hidden(X10,k5_xboole_0(X11,X12)))&(~r2_hidden(X10,X12)|r2_hidden(X10,X11)|r2_hidden(X10,k5_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.87/1.05  cnf(c_0_13, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.87/1.05  cnf(c_0_14, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.87/1.05  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.87/1.05  cnf(c_0_16, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.87/1.05  cnf(c_0_17, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.87/1.05  cnf(c_0_18, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)|r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.87/1.05  fof(c_0_19, negated_conjecture, ~(![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t96_xboole_1])).
% 0.87/1.05  cnf(c_0_20, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.87/1.05  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.87/1.05  cnf(c_0_22, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),k5_xboole_0(X1,X4))|r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X4)|r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.87/1.05  fof(c_0_23, negated_conjecture, ~r1_tarski(k4_xboole_0(esk3_0,esk4_0),k5_xboole_0(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.87/1.05  cnf(c_0_24, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_20, c_0_8])).
% 0.87/1.05  cnf(c_0_25, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,X2),k5_xboole_0(X1,X3)),X3)|r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.87/1.05  cnf(c_0_26, negated_conjecture, (~r1_tarski(k4_xboole_0(esk3_0,esk4_0),k5_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.87/1.05  cnf(c_0_27, plain, (r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.87/1.05  cnf(c_0_28, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27])]), ['proof']).
% 0.87/1.05  # SZS output end CNFRefutation
% 0.87/1.05  # Proof object total steps             : 29
% 0.87/1.05  # Proof object clause steps            : 16
% 0.87/1.05  # Proof object formula steps           : 13
% 0.87/1.05  # Proof object conjectures             : 5
% 0.87/1.05  # Proof object clause conjectures      : 2
% 0.87/1.05  # Proof object formula conjectures     : 3
% 0.87/1.05  # Proof object initial clauses used    : 8
% 0.87/1.05  # Proof object initial formulas used   : 6
% 0.87/1.05  # Proof object generating inferences   : 7
% 0.87/1.05  # Proof object simplifying inferences  : 2
% 0.87/1.05  # Training examples: 0 positive, 0 negative
% 0.87/1.05  # Parsed axioms                        : 6
% 0.87/1.05  # Removed by relevancy pruning/SinE    : 0
% 0.87/1.05  # Initial clauses                      : 13
% 0.87/1.05  # Removed in clause preprocessing      : 0
% 0.87/1.05  # Initial clauses in saturation        : 13
% 0.87/1.05  # Processed clauses                    : 2967
% 0.87/1.05  # ...of these trivial                  : 28
% 0.87/1.05  # ...subsumed                          : 845
% 0.87/1.05  # ...remaining for further processing  : 2094
% 0.87/1.05  # Other redundant clauses eliminated   : 0
% 0.87/1.05  # Clauses deleted for lack of memory   : 0
% 0.87/1.05  # Backward-subsumed                    : 35
% 0.87/1.05  # Backward-rewritten                   : 25
% 0.87/1.05  # Generated clauses                    : 65771
% 0.87/1.05  # ...of the previous two non-trivial   : 61958
% 0.87/1.05  # Contextual simplify-reflections      : 5
% 0.87/1.05  # Paramodulations                      : 65661
% 0.87/1.05  # Factorizations                       : 110
% 0.87/1.05  # Equation resolutions                 : 0
% 0.87/1.05  # Propositional unsat checks           : 0
% 0.87/1.05  #    Propositional check models        : 0
% 0.87/1.05  #    Propositional check unsatisfiable : 0
% 0.87/1.05  #    Propositional clauses             : 0
% 0.87/1.05  #    Propositional clauses after purity: 0
% 0.87/1.05  #    Propositional unsat core size     : 0
% 0.87/1.05  #    Propositional preprocessing time  : 0.000
% 0.87/1.05  #    Propositional encoding time       : 0.000
% 0.87/1.05  #    Propositional solver time         : 0.000
% 0.87/1.05  #    Success case prop preproc time    : 0.000
% 0.87/1.05  #    Success case prop encoding time   : 0.000
% 0.87/1.05  #    Success case prop solver time     : 0.000
% 0.87/1.05  # Current number of processed clauses  : 2021
% 0.87/1.05  #    Positive orientable unit clauses  : 1020
% 0.87/1.05  #    Positive unorientable unit clauses: 0
% 0.87/1.05  #    Negative unit clauses             : 1
% 0.87/1.05  #    Non-unit-clauses                  : 1000
% 0.87/1.05  # Current number of unprocessed clauses: 58905
% 0.87/1.05  # ...number of literals in the above   : 154779
% 0.87/1.05  # Current number of archived formulas  : 0
% 0.87/1.05  # Current number of archived clauses   : 73
% 0.87/1.05  # Clause-clause subsumption calls (NU) : 91346
% 0.87/1.05  # Rec. Clause-clause subsumption calls : 85911
% 0.87/1.05  # Non-unit clause-clause subsumptions  : 864
% 0.87/1.05  # Unit Clause-clause subsumption calls : 5759
% 0.87/1.05  # Rewrite failures with RHS unbound    : 0
% 0.87/1.05  # BW rewrite match attempts            : 21922
% 0.87/1.05  # BW rewrite match successes           : 37
% 0.87/1.05  # Condensation attempts                : 0
% 0.87/1.05  # Condensation successes               : 0
% 0.87/1.05  # Termbank termtop insertions          : 1391063
% 0.87/1.05  
% 0.87/1.05  # -------------------------------------------------
% 0.87/1.05  # User time                : 0.678 s
% 0.87/1.05  # System time              : 0.033 s
% 0.87/1.05  # Total time               : 0.711 s
% 0.87/1.05  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
