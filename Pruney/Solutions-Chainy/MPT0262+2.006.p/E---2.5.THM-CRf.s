%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:55 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  69 expanded)
%              Number of clauses        :   18 (  30 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 131 expanded)
%              Number of equality atoms :   12 (  32 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(l33_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t57_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X3,X2)
        & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(c_0_7,plain,(
    ! [X11,X12] : k2_tarski(X11,X12) = k2_xboole_0(k1_tarski(X11),k1_tarski(X12)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_8,plain,(
    ! [X13] : k2_tarski(X13,X13) = k1_tarski(X13) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_9,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_10,plain,(
    ! [X9,X10] : r1_xboole_0(k4_xboole_0(X9,X10),X10) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_11,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(k1_tarski(X14),X15) != k1_tarski(X14)
        | ~ r2_hidden(X14,X15) )
      & ( r2_hidden(X14,X15)
        | k4_xboole_0(k1_tarski(X14),X15) = k1_tarski(X14) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).

fof(c_0_12,plain,(
    ! [X6,X7,X8] :
      ( ( r1_xboole_0(X6,k2_xboole_0(X7,X8))
        | ~ r1_xboole_0(X6,X7)
        | ~ r1_xboole_0(X6,X8) )
      & ( r1_xboole_0(X6,X7)
        | ~ r1_xboole_0(X6,k2_xboole_0(X7,X8)) )
      & ( r1_xboole_0(X6,X8)
        | ~ r1_xboole_0(X6,k2_xboole_0(X7,X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_13,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),X2) = k2_tarski(X1,X1)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_14]),c_0_14])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,k2_tarski(X2,X3))
    | ~ r1_xboole_0(X1,k2_tarski(X3,X3))
    | ~ r1_xboole_0(X1,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(X2,k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X3,X2)
          & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t57_zfmisc_1])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(X2,k2_tarski(X3,X1))
    | ~ r1_xboole_0(X2,k2_tarski(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_26,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk2_0)
    & ~ r2_hidden(esk3_0,esk2_0)
    & ~ r1_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | r1_xboole_0(X2,k2_tarski(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | r1_xboole_0(k2_tarski(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053N
% 0.20/0.39  # and selection function HSelectMinInfpos.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.033 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.20/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.39  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.39  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.39  fof(l33_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 0.20/0.39  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.20/0.39  fof(t57_zfmisc_1, conjecture, ![X1, X2, X3]:~(((~(r2_hidden(X1,X2))&~(r2_hidden(X3,X2)))&~(r1_xboole_0(k2_tarski(X1,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 0.20/0.39  fof(c_0_7, plain, ![X11, X12]:k2_tarski(X11,X12)=k2_xboole_0(k1_tarski(X11),k1_tarski(X12)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.20/0.39  fof(c_0_8, plain, ![X13]:k2_tarski(X13,X13)=k1_tarski(X13), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.39  fof(c_0_9, plain, ![X4, X5]:(~r1_xboole_0(X4,X5)|r1_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.39  fof(c_0_10, plain, ![X9, X10]:r1_xboole_0(k4_xboole_0(X9,X10),X10), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.39  fof(c_0_11, plain, ![X14, X15]:((k4_xboole_0(k1_tarski(X14),X15)!=k1_tarski(X14)|~r2_hidden(X14,X15))&(r2_hidden(X14,X15)|k4_xboole_0(k1_tarski(X14),X15)=k1_tarski(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).
% 0.20/0.39  fof(c_0_12, plain, ![X6, X7, X8]:((r1_xboole_0(X6,k2_xboole_0(X7,X8))|~r1_xboole_0(X6,X7)|~r1_xboole_0(X6,X8))&((r1_xboole_0(X6,X7)|~r1_xboole_0(X6,k2_xboole_0(X7,X8)))&(r1_xboole_0(X6,X8)|~r1_xboole_0(X6,k2_xboole_0(X7,X8))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.20/0.39  cnf(c_0_13, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_14, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_15, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_16, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_17, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_18, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_19, plain, (k2_tarski(X1,X2)=k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_14])).
% 0.20/0.39  cnf(c_0_20, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.39  cnf(c_0_21, plain, (k4_xboole_0(k2_tarski(X1,X1),X2)=k2_tarski(X1,X1)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_14]), c_0_14])).
% 0.20/0.39  cnf(c_0_22, plain, (r1_xboole_0(X1,k2_tarski(X2,X3))|~r1_xboole_0(X1,k2_tarski(X3,X3))|~r1_xboole_0(X1,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.39  cnf(c_0_23, plain, (r2_hidden(X1,X2)|r1_xboole_0(X2,k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.39  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3]:~(((~(r2_hidden(X1,X2))&~(r2_hidden(X3,X2)))&~(r1_xboole_0(k2_tarski(X1,X3),X2))))), inference(assume_negation,[status(cth)],[t57_zfmisc_1])).
% 0.20/0.39  cnf(c_0_25, plain, (r2_hidden(X1,X2)|r1_xboole_0(X2,k2_tarski(X3,X1))|~r1_xboole_0(X2,k2_tarski(X3,X3))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.39  fof(c_0_26, negated_conjecture, ((~r2_hidden(esk1_0,esk2_0)&~r2_hidden(esk3_0,esk2_0))&~r1_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).
% 0.20/0.39  cnf(c_0_27, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|r1_xboole_0(X2,k2_tarski(X1,X3))), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 0.20/0.39  cnf(c_0_28, negated_conjecture, (~r1_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_29, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|r1_xboole_0(k2_tarski(X3,X1),X2)), inference(spm,[status(thm)],[c_0_15, c_0_27])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (~r2_hidden(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (~r2_hidden(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 33
% 0.20/0.39  # Proof object clause steps            : 18
% 0.20/0.39  # Proof object formula steps           : 15
% 0.20/0.39  # Proof object conjectures             : 7
% 0.20/0.39  # Proof object clause conjectures      : 4
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 9
% 0.20/0.39  # Proof object initial formulas used   : 7
% 0.20/0.39  # Proof object generating inferences   : 7
% 0.20/0.39  # Proof object simplifying inferences  : 6
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 7
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 12
% 0.20/0.39  # Removed in clause preprocessing      : 1
% 0.20/0.39  # Initial clauses in saturation        : 11
% 0.20/0.39  # Processed clauses                    : 62
% 0.20/0.39  # ...of these trivial                  : 4
% 0.20/0.39  # ...subsumed                          : 12
% 0.20/0.39  # ...remaining for further processing  : 46
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 0
% 0.20/0.39  # Generated clauses                    : 158
% 0.20/0.39  # ...of the previous two non-trivial   : 143
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 158
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 0
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 35
% 0.20/0.39  #    Positive orientable unit clauses  : 13
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 3
% 0.20/0.39  #    Non-unit-clauses                  : 19
% 0.20/0.39  # Current number of unprocessed clauses: 94
% 0.20/0.39  # ...number of literals in the above   : 182
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 12
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 109
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 94
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 12
% 0.20/0.39  # Unit Clause-clause subsumption calls : 2
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 5
% 0.20/0.39  # BW rewrite match successes           : 0
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 2232
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.039 s
% 0.20/0.39  # System time              : 0.003 s
% 0.20/0.39  # Total time               : 0.042 s
% 0.20/0.39  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
