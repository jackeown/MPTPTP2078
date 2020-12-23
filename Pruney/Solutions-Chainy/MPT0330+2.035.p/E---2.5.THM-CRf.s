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
% DateTime   : Thu Dec  3 10:44:30 EST 2020

% Result     : Theorem 8.58s
% Output     : CNFRefutation 8.58s
% Verified   : 
% Statistics : Number of formulae       :   39 (  87 expanded)
%              Number of clauses        :   24 (  38 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 131 expanded)
%              Number of equality atoms :   11 (  57 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t13_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

fof(c_0_7,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | r1_tarski(X7,k2_xboole_0(X9,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_8,plain,(
    ! [X19,X20] : k3_tarski(k2_tarski(X19,X20)) = k2_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X17,X18] : r1_tarski(X17,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_14,plain,(
    ! [X21,X22,X23] :
      ( k2_zfmisc_1(k2_xboole_0(X21,X22),X23) = k2_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(X22,X23))
      & k2_zfmisc_1(X23,k2_xboole_0(X21,X22)) = k2_xboole_0(k2_zfmisc_1(X23,X21),k2_zfmisc_1(X23,X22)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_tarski(X15,X16)
      | r1_tarski(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X10,X11,X12,X13] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(k2_xboole_0(X10,X12),k2_xboole_0(X11,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_12])).

cnf(c_0_23,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk5_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_12]),c_0_12])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),k3_tarski(k2_tarski(X2,X4)))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_12]),c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk1_0,k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(X1,esk2_0)),k3_tarski(k2_tarski(X2,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X3,esk6_0))))))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(esk4_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_25])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(esk4_0,X1))),k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X2,esk6_0)))))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_12]),c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_12]),c_0_12]),c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:57:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 8.58/8.77  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 8.58/8.77  # and selection function SelectDiffNegLit.
% 8.58/8.77  #
% 8.58/8.77  # Preprocessing time       : 0.027 s
% 8.58/8.77  # Presaturation interreduction done
% 8.58/8.77  
% 8.58/8.77  # Proof found!
% 8.58/8.77  # SZS status Theorem
% 8.58/8.77  # SZS output start CNFRefutation
% 8.58/8.77  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 8.58/8.77  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.58/8.77  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 8.58/8.77  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.58/8.77  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 8.58/8.77  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.58/8.77  fof(t13_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 8.58/8.77  fof(c_0_7, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|r1_tarski(X7,k2_xboole_0(X9,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 8.58/8.77  fof(c_0_8, plain, ![X19, X20]:k3_tarski(k2_tarski(X19,X20))=k2_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 8.58/8.77  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 8.58/8.77  fof(c_0_10, plain, ![X17, X18]:r1_tarski(X17,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 8.58/8.77  cnf(c_0_11, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 8.58/8.77  cnf(c_0_12, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 8.58/8.77  fof(c_0_13, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 8.58/8.77  fof(c_0_14, plain, ![X21, X22, X23]:(k2_zfmisc_1(k2_xboole_0(X21,X22),X23)=k2_xboole_0(k2_zfmisc_1(X21,X23),k2_zfmisc_1(X22,X23))&k2_zfmisc_1(X23,k2_xboole_0(X21,X22))=k2_xboole_0(k2_zfmisc_1(X23,X21),k2_zfmisc_1(X23,X22))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 8.58/8.77  fof(c_0_15, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|~r1_tarski(X15,X16)|r1_tarski(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 8.58/8.77  cnf(c_0_16, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 8.58/8.77  fof(c_0_17, plain, ![X10, X11, X12, X13]:(~r1_tarski(X10,X11)|~r1_tarski(X12,X13)|r1_tarski(k2_xboole_0(X10,X12),k2_xboole_0(X11,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).
% 8.58/8.77  cnf(c_0_18, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 8.58/8.77  cnf(c_0_19, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 8.58/8.77  cnf(c_0_20, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 8.58/8.77  cnf(c_0_21, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 8.58/8.77  cnf(c_0_22, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_16, c_0_12])).
% 8.58/8.77  cnf(c_0_23, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 8.58/8.77  cnf(c_0_24, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk5_0,esk6_0))))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 8.58/8.77  cnf(c_0_25, plain, (k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3)))=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_12]), c_0_12])).
% 8.58/8.77  cnf(c_0_26, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 8.58/8.77  cnf(c_0_27, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 8.58/8.77  cnf(c_0_28, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),k3_tarski(k2_tarski(X2,X4)))|~r1_tarski(X3,X4)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_12]), c_0_12])).
% 8.58/8.77  cnf(c_0_29, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0))))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 8.58/8.77  cnf(c_0_30, negated_conjecture, (r1_tarski(esk1_0,k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 8.58/8.77  cnf(c_0_31, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(X1,esk2_0)),k3_tarski(k2_tarski(X2,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X3,esk6_0))))))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 8.58/8.77  cnf(c_0_32, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(esk4_0,X1))))), inference(spm,[status(thm)],[c_0_30, c_0_25])).
% 8.58/8.77  cnf(c_0_33, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 8.58/8.77  cnf(c_0_34, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 8.58/8.77  cnf(c_0_35, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(esk4_0,X1))),k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X2,esk6_0))))))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 8.58/8.77  cnf(c_0_36, plain, (k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3)=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_12]), c_0_12])).
% 8.58/8.77  cnf(c_0_37, negated_conjecture, (~r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_12]), c_0_12]), c_0_12])).
% 8.58/8.77  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), ['proof']).
% 8.58/8.77  # SZS output end CNFRefutation
% 8.58/8.77  # Proof object total steps             : 39
% 8.58/8.77  # Proof object clause steps            : 24
% 8.58/8.77  # Proof object formula steps           : 15
% 8.58/8.77  # Proof object conjectures             : 14
% 8.58/8.77  # Proof object clause conjectures      : 11
% 8.58/8.77  # Proof object formula conjectures     : 3
% 8.58/8.77  # Proof object initial clauses used    : 10
% 8.58/8.77  # Proof object initial formulas used   : 7
% 8.58/8.77  # Proof object generating inferences   : 8
% 8.58/8.77  # Proof object simplifying inferences  : 12
% 8.58/8.77  # Training examples: 0 positive, 0 negative
% 8.58/8.77  # Parsed axioms                        : 7
% 8.58/8.77  # Removed by relevancy pruning/SinE    : 0
% 8.58/8.77  # Initial clauses                      : 10
% 8.58/8.77  # Removed in clause preprocessing      : 1
% 8.58/8.77  # Initial clauses in saturation        : 9
% 8.58/8.77  # Processed clauses                    : 6232
% 8.58/8.77  # ...of these trivial                  : 923
% 8.58/8.77  # ...subsumed                          : 495
% 8.58/8.77  # ...remaining for further processing  : 4814
% 8.58/8.77  # Other redundant clauses eliminated   : 0
% 8.58/8.77  # Clauses deleted for lack of memory   : 0
% 8.58/8.77  # Backward-subsumed                    : 189
% 8.58/8.77  # Backward-rewritten                   : 265
% 8.58/8.77  # Generated clauses                    : 881130
% 8.58/8.77  # ...of the previous two non-trivial   : 871439
% 8.58/8.77  # Contextual simplify-reflections      : 0
% 8.58/8.77  # Paramodulations                      : 881130
% 8.58/8.77  # Factorizations                       : 0
% 8.58/8.77  # Equation resolutions                 : 0
% 8.58/8.77  # Propositional unsat checks           : 0
% 8.58/8.77  #    Propositional check models        : 0
% 8.58/8.77  #    Propositional check unsatisfiable : 0
% 8.58/8.77  #    Propositional clauses             : 0
% 8.58/8.77  #    Propositional clauses after purity: 0
% 8.58/8.77  #    Propositional unsat core size     : 0
% 8.58/8.77  #    Propositional preprocessing time  : 0.000
% 8.58/8.77  #    Propositional encoding time       : 0.000
% 8.58/8.77  #    Propositional solver time         : 0.000
% 8.58/8.77  #    Success case prop preproc time    : 0.000
% 8.58/8.77  #    Success case prop encoding time   : 0.000
% 8.58/8.77  #    Success case prop solver time     : 0.000
% 8.58/8.77  # Current number of processed clauses  : 4351
% 8.58/8.77  #    Positive orientable unit clauses  : 2347
% 8.58/8.77  #    Positive unorientable unit clauses: 10
% 8.58/8.77  #    Negative unit clauses             : 1
% 8.58/8.77  #    Non-unit-clauses                  : 1993
% 8.58/8.77  # Current number of unprocessed clauses: 864385
% 8.58/8.77  # ...number of literals in the above   : 872694
% 8.58/8.77  # Current number of archived formulas  : 0
% 8.58/8.77  # Current number of archived clauses   : 464
% 8.58/8.77  # Clause-clause subsumption calls (NU) : 811535
% 8.58/8.77  # Rec. Clause-clause subsumption calls : 810417
% 8.58/8.77  # Non-unit clause-clause subsumptions  : 683
% 8.58/8.77  # Unit Clause-clause subsumption calls : 19428
% 8.58/8.77  # Rewrite failures with RHS unbound    : 0
% 8.58/8.77  # BW rewrite match attempts            : 1451319
% 8.58/8.77  # BW rewrite match successes           : 461
% 8.58/8.77  # Condensation attempts                : 0
% 8.58/8.77  # Condensation successes               : 0
% 8.58/8.77  # Termbank termtop insertions          : 32253204
% 8.58/8.81  
% 8.58/8.81  # -------------------------------------------------
% 8.58/8.81  # User time                : 8.014 s
% 8.58/8.81  # System time              : 0.446 s
% 8.58/8.81  # Total time               : 8.460 s
% 8.58/8.81  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
