%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:12 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   25 (  57 expanded)
%              Number of clauses        :   16 (  30 expanded)
%              Number of leaves         :    4 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 ( 311 expanded)
%              Number of equality atoms :   28 ( 104 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t98_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(assume_negation,[status(cth)],[t98_xboole_1])).

cnf(c_0_6,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,(
    k2_xboole_0(esk2_0,esk3_0) != k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X14,X15] : k5_xboole_0(X14,X15) = k2_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_10,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) != k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(k4_xboole_0(X1,X2),X3,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_11]),c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),k4_xboole_0(k4_xboole_0(esk3_0,esk2_0),esk2_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = X1
    | ~ r2_hidden(esk1_3(X1,k4_xboole_0(X2,X3),X1),X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_16])).

fof(c_0_20,plain,(
    ! [X16,X17] : k2_xboole_0(X16,k4_xboole_0(X17,X16)) = k2_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_21,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),k4_xboole_0(esk3_0,esk2_0)) != k2_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_19,c_0_11])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:41:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.20/0.40  # and selection function SelectComplexExceptRRHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.026 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.40  fof(t98_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.40  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.20/0.40  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.40  fof(c_0_4, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.40  fof(c_0_5, negated_conjecture, ~(![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(assume_negation,[status(cth)],[t98_xboole_1])).
% 0.20/0.40  cnf(c_0_6, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.40  cnf(c_0_7, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.40  fof(c_0_8, negated_conjecture, k2_xboole_0(esk2_0,esk3_0)!=k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.20/0.40  fof(c_0_9, plain, ![X14, X15]:k5_xboole_0(X14,X15)=k2_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.20/0.40  cnf(c_0_10, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_6])).
% 0.20/0.40  cnf(c_0_11, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_7])).
% 0.20/0.40  cnf(c_0_12, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.40  cnf(c_0_13, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)!=k5_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_14, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_15, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(k4_xboole_0(X1,X2),X3,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.40  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_11]), c_0_11])).
% 0.20/0.40  cnf(c_0_17, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),k4_xboole_0(k4_xboole_0(esk3_0,esk2_0),esk2_0))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.40  cnf(c_0_18, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.40  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=X1|~r2_hidden(esk1_3(X1,k4_xboole_0(X2,X3),X1),X3)), inference(spm,[status(thm)],[c_0_10, c_0_16])).
% 0.20/0.40  fof(c_0_20, plain, ![X16, X17]:k2_xboole_0(X16,k4_xboole_0(X17,X16))=k2_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.40  cnf(c_0_21, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk3_0,esk2_0)),k4_xboole_0(esk3_0,esk2_0))!=k2_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.40  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_19, c_0_11])).
% 0.20/0.40  cnf(c_0_23, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_24, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 25
% 0.20/0.40  # Proof object clause steps            : 16
% 0.20/0.40  # Proof object formula steps           : 9
% 0.20/0.40  # Proof object conjectures             : 7
% 0.20/0.40  # Proof object clause conjectures      : 4
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 6
% 0.20/0.40  # Proof object initial formulas used   : 4
% 0.20/0.40  # Proof object generating inferences   : 6
% 0.20/0.40  # Proof object simplifying inferences  : 7
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 4
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 9
% 0.20/0.40  # Removed in clause preprocessing      : 1
% 0.20/0.40  # Initial clauses in saturation        : 8
% 0.20/0.40  # Processed clauses                    : 559
% 0.20/0.40  # ...of these trivial                  : 9
% 0.20/0.40  # ...subsumed                          : 467
% 0.20/0.40  # ...remaining for further processing  : 83
% 0.20/0.40  # Other redundant clauses eliminated   : 3
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 5
% 0.20/0.40  # Generated clauses                    : 2127
% 0.20/0.40  # ...of the previous two non-trivial   : 1871
% 0.20/0.40  # Contextual simplify-reflections      : 2
% 0.20/0.40  # Paramodulations                      : 2098
% 0.20/0.40  # Factorizations                       : 26
% 0.20/0.40  # Equation resolutions                 : 3
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 67
% 0.20/0.40  #    Positive orientable unit clauses  : 8
% 0.20/0.40  #    Positive unorientable unit clauses: 6
% 0.20/0.40  #    Negative unit clauses             : 6
% 0.20/0.40  #    Non-unit-clauses                  : 47
% 0.20/0.40  # Current number of unprocessed clauses: 1300
% 0.20/0.40  # ...number of literals in the above   : 3501
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 14
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 1547
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 756
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 51
% 0.20/0.40  # Unit Clause-clause subsumption calls : 165
% 0.20/0.40  # Rewrite failures with RHS unbound    : 204
% 0.20/0.40  # BW rewrite match attempts            : 155
% 0.20/0.40  # BW rewrite match successes           : 23
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 23948
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.054 s
% 0.20/0.40  # System time              : 0.005 s
% 0.20/0.40  # Total time               : 0.059 s
% 0.20/0.40  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
