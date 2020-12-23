%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:13 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 132 expanded)
%              Number of clauses        :   22 (  59 expanded)
%              Number of leaves         :    6 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   64 ( 249 expanded)
%              Number of equality atoms :   33 ( 129 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(t67_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X2,X3) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X3) )
       => r1_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t73_xboole_1])).

fof(c_0_7,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X13,X15)
      | ~ r1_xboole_0(X14,X15)
      | X13 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).

fof(c_0_8,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    & r1_xboole_0(esk1_0,esk3_0)
    & ~ r1_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_9,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_12,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X11,X12] : k4_xboole_0(X11,k2_xboole_0(X11,X12)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_15,plain,(
    ! [X8,X9,X10] : k4_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_16,negated_conjecture,
    ( X1 = k1_xboole_0
    | k4_xboole_0(X1,esk3_0) != k1_xboole_0
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_20,negated_conjecture,
    ( X1 = k1_xboole_0
    | k4_xboole_0(X1,esk3_0) != k1_xboole_0
    | k4_xboole_0(X1,esk1_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_13])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_21])])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_22]),c_0_18])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | k4_xboole_0(k4_xboole_0(X1,esk3_0),X2) != k1_xboole_0
    | k4_xboole_0(k4_xboole_0(X1,X2),esk1_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk1_0,esk3_0),esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n010.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 17:16:14 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.11/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S061I
% 0.11/0.35  # and selection function SelectMaxLComplexAPPNTNp.
% 0.11/0.35  #
% 0.11/0.35  # Preprocessing time       : 0.028 s
% 0.11/0.35  # Presaturation interreduction done
% 0.11/0.35  
% 0.11/0.35  # Proof found!
% 0.11/0.35  # SZS status Theorem
% 0.11/0.35  # SZS output start CNFRefutation
% 0.11/0.35  fof(t73_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.11/0.35  fof(t67_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&r1_xboole_0(X2,X3))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 0.11/0.35  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.11/0.35  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.11/0.35  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.11/0.35  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.11/0.35  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2))), inference(assume_negation,[status(cth)],[t73_xboole_1])).
% 0.11/0.35  fof(c_0_7, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X13,X15)|~r1_xboole_0(X14,X15)|X13=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).
% 0.11/0.35  fof(c_0_8, negated_conjecture, ((r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))&r1_xboole_0(esk1_0,esk3_0))&~r1_tarski(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.11/0.35  cnf(c_0_9, plain, (X1=k1_xboole_0|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.11/0.35  cnf(c_0_10, negated_conjecture, (r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.11/0.35  fof(c_0_11, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.11/0.35  cnf(c_0_12, negated_conjecture, (X1=k1_xboole_0|~r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.11/0.35  cnf(c_0_13, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.35  fof(c_0_14, plain, ![X11, X12]:k4_xboole_0(X11,k2_xboole_0(X11,X12))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.11/0.35  fof(c_0_15, plain, ![X8, X9, X10]:k4_xboole_0(k4_xboole_0(X8,X9),X10)=k4_xboole_0(X8,k2_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.11/0.35  cnf(c_0_16, negated_conjecture, (X1=k1_xboole_0|k4_xboole_0(X1,esk3_0)!=k1_xboole_0|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.11/0.35  cnf(c_0_17, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.35  cnf(c_0_18, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.35  fof(c_0_19, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.11/0.35  cnf(c_0_20, negated_conjecture, (X1=k1_xboole_0|k4_xboole_0(X1,esk3_0)!=k1_xboole_0|k4_xboole_0(X1,esk1_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_13])).
% 0.11/0.35  cnf(c_0_21, plain, (k4_xboole_0(k4_xboole_0(X1,X1),X2)=k1_xboole_0), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.11/0.35  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.11/0.35  cnf(c_0_23, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.11/0.35  cnf(c_0_24, negated_conjecture, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_21])])).
% 0.11/0.35  cnf(c_0_25, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k4_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_22]), c_0_18])).
% 0.11/0.35  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.35  cnf(c_0_27, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(esk3_0,esk2_0))), inference(rw,[status(thm)],[c_0_23, c_0_22])).
% 0.11/0.35  cnf(c_0_28, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_21, c_0_24])).
% 0.11/0.35  cnf(c_0_29, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.11/0.35  cnf(c_0_30, negated_conjecture, (k4_xboole_0(X1,X2)=k1_xboole_0|k4_xboole_0(k4_xboole_0(X1,esk3_0),X2)!=k1_xboole_0|k4_xboole_0(k4_xboole_0(X1,X2),esk1_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_25])).
% 0.11/0.35  cnf(c_0_31, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk1_0,esk3_0),esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_18])).
% 0.11/0.35  cnf(c_0_32, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_24]), c_0_28])).
% 0.11/0.35  cnf(c_0_33, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_13])).
% 0.11/0.35  cnf(c_0_34, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])]), c_0_33]), ['proof']).
% 0.11/0.35  # SZS output end CNFRefutation
% 0.11/0.35  # Proof object total steps             : 35
% 0.11/0.35  # Proof object clause steps            : 22
% 0.11/0.35  # Proof object formula steps           : 13
% 0.11/0.35  # Proof object conjectures             : 16
% 0.11/0.35  # Proof object clause conjectures      : 13
% 0.11/0.35  # Proof object formula conjectures     : 3
% 0.11/0.35  # Proof object initial clauses used    : 9
% 0.11/0.35  # Proof object initial formulas used   : 6
% 0.11/0.35  # Proof object generating inferences   : 10
% 0.11/0.35  # Proof object simplifying inferences  : 11
% 0.11/0.35  # Training examples: 0 positive, 0 negative
% 0.11/0.35  # Parsed axioms                        : 6
% 0.11/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.35  # Initial clauses                      : 9
% 0.11/0.35  # Removed in clause preprocessing      : 0
% 0.11/0.35  # Initial clauses in saturation        : 9
% 0.11/0.35  # Processed clauses                    : 52
% 0.11/0.35  # ...of these trivial                  : 3
% 0.11/0.35  # ...subsumed                          : 8
% 0.11/0.35  # ...remaining for further processing  : 41
% 0.11/0.35  # Other redundant clauses eliminated   : 0
% 0.11/0.35  # Clauses deleted for lack of memory   : 0
% 0.11/0.35  # Backward-subsumed                    : 0
% 0.11/0.35  # Backward-rewritten                   : 3
% 0.11/0.35  # Generated clauses                    : 139
% 0.11/0.35  # ...of the previous two non-trivial   : 99
% 0.11/0.35  # Contextual simplify-reflections      : 0
% 0.11/0.35  # Paramodulations                      : 139
% 0.11/0.35  # Factorizations                       : 0
% 0.11/0.35  # Equation resolutions                 : 0
% 0.11/0.35  # Propositional unsat checks           : 0
% 0.11/0.35  #    Propositional check models        : 0
% 0.11/0.35  #    Propositional check unsatisfiable : 0
% 0.11/0.35  #    Propositional clauses             : 0
% 0.11/0.35  #    Propositional clauses after purity: 0
% 0.11/0.35  #    Propositional unsat core size     : 0
% 0.11/0.35  #    Propositional preprocessing time  : 0.000
% 0.11/0.35  #    Propositional encoding time       : 0.000
% 0.11/0.35  #    Propositional solver time         : 0.000
% 0.11/0.35  #    Success case prop preproc time    : 0.000
% 0.11/0.35  #    Success case prop encoding time   : 0.000
% 0.11/0.35  #    Success case prop solver time     : 0.000
% 0.11/0.35  # Current number of processed clauses  : 29
% 0.11/0.35  #    Positive orientable unit clauses  : 13
% 0.11/0.35  #    Positive unorientable unit clauses: 2
% 0.11/0.35  #    Negative unit clauses             : 2
% 0.11/0.35  #    Non-unit-clauses                  : 12
% 0.11/0.35  # Current number of unprocessed clauses: 53
% 0.11/0.35  # ...number of literals in the above   : 64
% 0.11/0.35  # Current number of archived formulas  : 0
% 0.11/0.35  # Current number of archived clauses   : 12
% 0.11/0.35  # Clause-clause subsumption calls (NU) : 44
% 0.11/0.35  # Rec. Clause-clause subsumption calls : 44
% 0.11/0.35  # Non-unit clause-clause subsumptions  : 7
% 0.11/0.35  # Unit Clause-clause subsumption calls : 1
% 0.11/0.35  # Rewrite failures with RHS unbound    : 0
% 0.11/0.35  # BW rewrite match attempts            : 46
% 0.11/0.35  # BW rewrite match successes           : 24
% 0.11/0.35  # Condensation attempts                : 0
% 0.11/0.35  # Condensation successes               : 0
% 0.11/0.35  # Termbank termtop insertions          : 1810
% 0.11/0.35  
% 0.11/0.35  # -------------------------------------------------
% 0.11/0.35  # User time                : 0.028 s
% 0.11/0.35  # System time              : 0.006 s
% 0.11/0.35  # Total time               : 0.034 s
% 0.11/0.35  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
