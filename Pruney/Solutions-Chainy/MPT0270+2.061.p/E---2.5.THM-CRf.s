%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:44 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 101 expanded)
%              Number of clauses        :   22 (  46 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 182 expanded)
%              Number of equality atoms :   49 ( 114 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t88_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(t93_enumset1,axiom,(
    ! [X1,X2,X3] : k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_enumset1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t67_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(t56_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(l35_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(c_0_10,plain,(
    ! [X22,X23] : k3_tarski(k2_tarski(X22,X23)) = k2_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | k4_xboole_0(k2_xboole_0(X6,X7),X7) = X6 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).

cnf(c_0_13,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X17,X18,X19] : k6_enumset1(X17,X17,X17,X17,X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t93_enumset1])).

fof(c_0_16,plain,(
    ! [X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),X5) = k4_xboole_0(X4,X5) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_17,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
      <=> ~ r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t67_zfmisc_1])).

cnf(c_0_22,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_18]),c_0_19])).

fof(c_0_24,plain,(
    ! [X24,X25] :
      ( r2_hidden(X24,X25)
      | r1_xboole_0(k1_tarski(X24),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_zfmisc_1])])])).

fof(c_0_25,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X8
        | X9 != k1_tarski(X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k1_tarski(X8) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | esk1_2(X12,X13) != X12
        | X13 = k1_tarski(X12) )
      & ( r2_hidden(esk1_2(X12,X13),X13)
        | esk1_2(X12,X13) = X12
        | X13 = k1_tarski(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_26,negated_conjecture,
    ( ( k4_xboole_0(k1_tarski(esk2_0),esk3_0) != k1_tarski(esk2_0)
      | r2_hidden(esk2_0,esk3_0) )
    & ( k4_xboole_0(k1_tarski(esk2_0),esk3_0) = k1_tarski(esk2_0)
      | ~ r2_hidden(esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X20,X21] :
      ( ( k4_xboole_0(k1_tarski(X20),X21) != k1_xboole_0
        | r2_hidden(X20,X21) )
      & ( ~ r2_hidden(X20,X21)
        | k4_xboole_0(k1_tarski(X20),X21) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | k4_xboole_0(k1_tarski(esk2_0),esk3_0) != k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_33,plain,(
    ! [X26,X27] :
      ( ( k4_xboole_0(X26,k1_tarski(X27)) != X26
        | ~ r2_hidden(X27,X26) )
      & ( r2_hidden(X27,X26)
        | k4_xboole_0(X26,k1_tarski(X27)) = X26 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk2_0),esk3_0) = k1_tarski(esk2_0)
    | ~ r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk2_0),esk3_0) = k1_tarski(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_41,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_35])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_37]),c_0_40]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:47:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.20/0.38  # and selection function SelectCQIArNpEqFirst.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.026 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(t88_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 0.20/0.38  fof(t93_enumset1, axiom, ![X1, X2, X3]:k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_enumset1)).
% 0.20/0.38  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.20/0.38  fof(t67_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 0.20/0.38  fof(t56_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_zfmisc_1)).
% 0.20/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.38  fof(l35_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 0.20/0.38  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.20/0.38  fof(c_0_10, plain, ![X22, X23]:k3_tarski(k2_tarski(X22,X23))=k2_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.38  fof(c_0_11, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_12, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|k4_xboole_0(k2_xboole_0(X6,X7),X7)=X6), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).
% 0.20/0.38  cnf(c_0_13, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  fof(c_0_15, plain, ![X17, X18, X19]:k6_enumset1(X17,X17,X17,X17,X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t93_enumset1])).
% 0.20/0.38  fof(c_0_16, plain, ![X4, X5]:k4_xboole_0(k2_xboole_0(X4,X5),X5)=k4_xboole_0(X4,X5), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.20/0.38  cnf(c_0_17, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_18, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.38  cnf(c_0_19, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_20, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  fof(c_0_21, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2)))), inference(assume_negation,[status(cth)],[t67_zfmisc_1])).
% 0.20/0.38  cnf(c_0_22, plain, (k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.20/0.38  cnf(c_0_23, plain, (k4_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_18]), c_0_19])).
% 0.20/0.38  fof(c_0_24, plain, ![X24, X25]:(r2_hidden(X24,X25)|r1_xboole_0(k1_tarski(X24),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_zfmisc_1])])])).
% 0.20/0.38  fof(c_0_25, plain, ![X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X10,X9)|X10=X8|X9!=k1_tarski(X8))&(X11!=X8|r2_hidden(X11,X9)|X9!=k1_tarski(X8)))&((~r2_hidden(esk1_2(X12,X13),X13)|esk1_2(X12,X13)!=X12|X13=k1_tarski(X12))&(r2_hidden(esk1_2(X12,X13),X13)|esk1_2(X12,X13)=X12|X13=k1_tarski(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.38  fof(c_0_26, negated_conjecture, ((k4_xboole_0(k1_tarski(esk2_0),esk3_0)!=k1_tarski(esk2_0)|r2_hidden(esk2_0,esk3_0))&(k4_xboole_0(k1_tarski(esk2_0),esk3_0)=k1_tarski(esk2_0)|~r2_hidden(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.20/0.38  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.38  cnf(c_0_28, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  fof(c_0_29, plain, ![X20, X21]:((k4_xboole_0(k1_tarski(X20),X21)!=k1_xboole_0|r2_hidden(X20,X21))&(~r2_hidden(X20,X21)|k4_xboole_0(k1_tarski(X20),X21)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).
% 0.20/0.38  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|k4_xboole_0(k1_tarski(esk2_0),esk3_0)!=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_32, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.38  fof(c_0_33, plain, ![X26, X27]:((k4_xboole_0(X26,k1_tarski(X27))!=X26|~r2_hidden(X27,X26))&(r2_hidden(X27,X26)|k4_xboole_0(X26,k1_tarski(X27))=X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.20/0.38  cnf(c_0_34, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.38  cnf(c_0_35, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (k4_xboole_0(k1_tarski(esk2_0),esk3_0)=k1_tarski(esk2_0)|~r2_hidden(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.38  cnf(c_0_38, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.38  cnf(c_0_39, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (k4_xboole_0(k1_tarski(esk2_0),esk3_0)=k1_tarski(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37])])).
% 0.20/0.38  cnf(c_0_41, plain, (k1_tarski(X1)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_35])])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_37]), c_0_40]), c_0_41]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 43
% 0.20/0.38  # Proof object clause steps            : 22
% 0.20/0.38  # Proof object formula steps           : 21
% 0.20/0.38  # Proof object conjectures             : 8
% 0.20/0.38  # Proof object clause conjectures      : 5
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 11
% 0.20/0.38  # Proof object initial formulas used   : 10
% 0.20/0.38  # Proof object generating inferences   : 5
% 0.20/0.38  # Proof object simplifying inferences  : 14
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 10
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 16
% 0.20/0.38  # Removed in clause preprocessing      : 3
% 0.20/0.38  # Initial clauses in saturation        : 13
% 0.20/0.38  # Processed clauses                    : 37
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 36
% 0.20/0.38  # Other redundant clauses eliminated   : 3
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 2
% 0.20/0.38  # Generated clauses                    : 24
% 0.20/0.38  # ...of the previous two non-trivial   : 19
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 22
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 3
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 19
% 0.20/0.38  #    Positive orientable unit clauses  : 5
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 13
% 0.20/0.38  # Current number of unprocessed clauses: 8
% 0.20/0.38  # ...number of literals in the above   : 22
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 18
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 47
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 42
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.38  # Unit Clause-clause subsumption calls : 5
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 1
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 1232
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.029 s
% 0.20/0.38  # System time              : 0.002 s
% 0.20/0.38  # Total time               : 0.031 s
% 0.20/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
