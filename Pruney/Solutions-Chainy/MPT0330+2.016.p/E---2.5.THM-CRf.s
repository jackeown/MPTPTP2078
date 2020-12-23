%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:27 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   36 (  94 expanded)
%              Number of clauses        :   23 (  41 expanded)
%              Number of leaves         :    6 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 ( 135 expanded)
%              Number of equality atoms :   15 (  67 expanded)
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

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(t13_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_6,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | r1_tarski(X9,k2_xboole_0(X11,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_7,plain,(
    ! [X16,X17] : k3_tarski(k2_tarski(X16,X17)) = k2_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_12,plain,(
    ! [X18,X19,X20] :
      ( k2_zfmisc_1(k2_xboole_0(X18,X19),X20) = k2_xboole_0(k2_zfmisc_1(X18,X20),k2_zfmisc_1(X19,X20))
      & k2_zfmisc_1(X20,k2_xboole_0(X18,X19)) = k2_xboole_0(k2_zfmisc_1(X20,X18),k2_zfmisc_1(X20,X19)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X12,X13,X14,X15] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(k2_xboole_0(X12,X14),k2_xboole_0(X13,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_19,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk5_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_10]),c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk1_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_17])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),k3_tarski(k2_tarski(X2,X4)))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_10]),c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_27,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_10]),c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(X1,esk2_0)),k3_tarski(k2_tarski(X2,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X3,esk6_0))))))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(esk4_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(esk4_0,X1))),k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X2,esk6_0)))))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_10]),c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_10]),c_0_10]),c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:00:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.48/0.65  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.48/0.65  # and selection function SelectDiffNegLit.
% 0.48/0.65  #
% 0.48/0.65  # Preprocessing time       : 0.026 s
% 0.48/0.65  # Presaturation interreduction done
% 0.48/0.65  
% 0.48/0.65  # Proof found!
% 0.48/0.65  # SZS status Theorem
% 0.48/0.65  # SZS output start CNFRefutation
% 0.48/0.65  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.48/0.65  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.48/0.65  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 0.48/0.65  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 0.48/0.65  fof(t13_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 0.48/0.65  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.48/0.65  fof(c_0_6, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|r1_tarski(X9,k2_xboole_0(X11,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.48/0.65  fof(c_0_7, plain, ![X16, X17]:k3_tarski(k2_tarski(X16,X17))=k2_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.48/0.65  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 0.48/0.65  cnf(c_0_9, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.48/0.65  cnf(c_0_10, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.48/0.65  fof(c_0_11, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.48/0.65  fof(c_0_12, plain, ![X18, X19, X20]:(k2_zfmisc_1(k2_xboole_0(X18,X19),X20)=k2_xboole_0(k2_zfmisc_1(X18,X20),k2_zfmisc_1(X19,X20))&k2_zfmisc_1(X20,k2_xboole_0(X18,X19))=k2_xboole_0(k2_zfmisc_1(X20,X18),k2_zfmisc_1(X20,X19))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 0.48/0.65  fof(c_0_13, plain, ![X12, X13, X14, X15]:(~r1_tarski(X12,X13)|~r1_tarski(X14,X15)|r1_tarski(k2_xboole_0(X12,X14),k2_xboole_0(X13,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).
% 0.48/0.65  cnf(c_0_14, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.48/0.65  cnf(c_0_15, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.48/0.65  cnf(c_0_16, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.65  cnf(c_0_17, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.48/0.65  fof(c_0_18, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k2_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.48/0.65  cnf(c_0_19, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.48/0.65  cnf(c_0_20, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk5_0,esk6_0))))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.48/0.65  cnf(c_0_21, plain, (k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3)))=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_10]), c_0_10])).
% 0.48/0.65  cnf(c_0_22, negated_conjecture, (r1_tarski(esk1_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0))))), inference(spm,[status(thm)],[c_0_14, c_0_17])).
% 0.48/0.65  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.48/0.65  cnf(c_0_24, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),k3_tarski(k2_tarski(X2,X4)))|~r1_tarski(X3,X4)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_10]), c_0_10])).
% 0.48/0.65  cnf(c_0_25, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0))))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.48/0.65  cnf(c_0_26, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0))))), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.48/0.65  cnf(c_0_27, plain, (k3_tarski(k2_tarski(X1,X2))=k3_tarski(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_10]), c_0_10])).
% 0.48/0.65  cnf(c_0_28, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(X1,esk2_0)),k3_tarski(k2_tarski(X2,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X3,esk6_0))))))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.48/0.65  cnf(c_0_29, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(esk4_0,X1))))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.48/0.65  cnf(c_0_30, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.65  cnf(c_0_31, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.48/0.65  cnf(c_0_32, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(esk4_0,X1))),k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X2,esk6_0))))))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.48/0.65  cnf(c_0_33, plain, (k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3)=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_10]), c_0_10])).
% 0.48/0.65  cnf(c_0_34, negated_conjecture, (~r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_10]), c_0_10]), c_0_10])).
% 0.48/0.65  cnf(c_0_35, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), ['proof']).
% 0.48/0.65  # SZS output end CNFRefutation
% 0.48/0.65  # Proof object total steps             : 36
% 0.48/0.65  # Proof object clause steps            : 23
% 0.48/0.65  # Proof object formula steps           : 13
% 0.48/0.65  # Proof object conjectures             : 15
% 0.48/0.65  # Proof object clause conjectures      : 12
% 0.48/0.65  # Proof object formula conjectures     : 3
% 0.48/0.65  # Proof object initial clauses used    : 9
% 0.48/0.65  # Proof object initial formulas used   : 6
% 0.48/0.65  # Proof object generating inferences   : 8
% 0.48/0.65  # Proof object simplifying inferences  : 13
% 0.48/0.65  # Training examples: 0 positive, 0 negative
% 0.48/0.65  # Parsed axioms                        : 6
% 0.48/0.65  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.65  # Initial clauses                      : 9
% 0.48/0.65  # Removed in clause preprocessing      : 1
% 0.48/0.65  # Initial clauses in saturation        : 8
% 0.48/0.65  # Processed clauses                    : 820
% 0.48/0.65  # ...of these trivial                  : 356
% 0.48/0.65  # ...subsumed                          : 8
% 0.48/0.65  # ...remaining for further processing  : 456
% 0.48/0.65  # Other redundant clauses eliminated   : 0
% 0.48/0.65  # Clauses deleted for lack of memory   : 0
% 0.48/0.65  # Backward-subsumed                    : 0
% 0.48/0.65  # Backward-rewritten                   : 13
% 0.48/0.65  # Generated clauses                    : 28391
% 0.48/0.65  # ...of the previous two non-trivial   : 26961
% 0.48/0.65  # Contextual simplify-reflections      : 0
% 0.48/0.65  # Paramodulations                      : 28391
% 0.48/0.65  # Factorizations                       : 0
% 0.48/0.65  # Equation resolutions                 : 0
% 0.48/0.65  # Propositional unsat checks           : 0
% 0.48/0.65  #    Propositional check models        : 0
% 0.48/0.65  #    Propositional check unsatisfiable : 0
% 0.48/0.65  #    Propositional clauses             : 0
% 0.48/0.65  #    Propositional clauses after purity: 0
% 0.48/0.65  #    Propositional unsat core size     : 0
% 0.48/0.65  #    Propositional preprocessing time  : 0.000
% 0.48/0.65  #    Propositional encoding time       : 0.000
% 0.48/0.65  #    Propositional solver time         : 0.000
% 0.48/0.65  #    Success case prop preproc time    : 0.000
% 0.48/0.65  #    Success case prop encoding time   : 0.000
% 0.48/0.65  #    Success case prop solver time     : 0.000
% 0.48/0.65  # Current number of processed clauses  : 435
% 0.48/0.65  #    Positive orientable unit clauses  : 362
% 0.48/0.65  #    Positive unorientable unit clauses: 2
% 0.48/0.65  #    Negative unit clauses             : 1
% 0.48/0.65  #    Non-unit-clauses                  : 70
% 0.48/0.65  # Current number of unprocessed clauses: 26069
% 0.48/0.65  # ...number of literals in the above   : 26371
% 0.48/0.65  # Current number of archived formulas  : 0
% 0.48/0.65  # Current number of archived clauses   : 22
% 0.48/0.65  # Clause-clause subsumption calls (NU) : 1838
% 0.48/0.65  # Rec. Clause-clause subsumption calls : 1838
% 0.48/0.65  # Non-unit clause-clause subsumptions  : 0
% 0.48/0.65  # Unit Clause-clause subsumption calls : 2293
% 0.48/0.65  # Rewrite failures with RHS unbound    : 0
% 0.48/0.65  # BW rewrite match attempts            : 21327
% 0.48/0.65  # BW rewrite match successes           : 29
% 0.48/0.65  # Condensation attempts                : 0
% 0.48/0.65  # Condensation successes               : 0
% 0.48/0.65  # Termbank termtop insertions          : 869431
% 0.48/0.65  
% 0.48/0.65  # -------------------------------------------------
% 0.48/0.65  # User time                : 0.274 s
% 0.48/0.65  # System time              : 0.033 s
% 0.48/0.65  # Total time               : 0.308 s
% 0.48/0.65  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
