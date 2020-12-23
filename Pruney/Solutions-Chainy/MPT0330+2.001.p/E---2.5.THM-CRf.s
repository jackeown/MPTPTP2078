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
% DateTime   : Thu Dec  3 10:44:25 EST 2020

% Result     : Theorem 5.77s
% Output     : CNFRefutation 5.77s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 164 expanded)
%              Number of clauses        :   27 (  75 expanded)
%              Number of leaves         :    8 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :   68 ( 211 expanded)
%              Number of equality atoms :   19 ( 129 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(t13_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_8,plain,(
    ! [X29,X30] : k3_tarski(k2_tarski(X29,X30)) = k2_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X27,X28] : k1_enumset1(X27,X27,X28) = k2_tarski(X27,X28) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_10,plain,(
    ! [X23,X24] : r1_tarski(X23,k2_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_11,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,X19)
      | ~ r1_tarski(X19,X20)
      | r1_tarski(X18,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_20,plain,(
    ! [X31,X32,X33] :
      ( k2_zfmisc_1(k2_xboole_0(X31,X32),X33) = k2_xboole_0(k2_zfmisc_1(X31,X33),k2_zfmisc_1(X32,X33))
      & k2_zfmisc_1(X33,k2_xboole_0(X31,X32)) = k2_xboole_0(k2_zfmisc_1(X33,X31),k2_zfmisc_1(X33,X32)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X14,X15,X16,X17] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_tarski(X16,X17)
      | r1_tarski(k2_xboole_0(X14,X16),k2_xboole_0(X15,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X25,X26] : k2_tarski(X25,X26) = k2_tarski(X26,X25) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k1_enumset1(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0),X1))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_15]),c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk1_0,k3_tarski(k1_enumset1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),X1))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_25])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),k3_tarski(k1_enumset1(X2,X2,X4)))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_15]),c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_35,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_12]),c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,esk2_0)),k3_tarski(k1_enumset1(X2,X2,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X3))))))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k3_tarski(k1_enumset1(k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0))),k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0))),k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X2)))))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X2)),X3) = k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_15]),c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k1_enumset1(esk3_0,esk3_0,esk5_0)),k3_tarski(k1_enumset1(esk4_0,esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_15]),c_0_15]),c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_35]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 5.77/5.99  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 5.77/5.99  # and selection function SelectCQArNTNp.
% 5.77/5.99  #
% 5.77/5.99  # Preprocessing time       : 0.027 s
% 5.77/5.99  # Presaturation interreduction done
% 5.77/5.99  
% 5.77/5.99  # Proof found!
% 5.77/5.99  # SZS status Theorem
% 5.77/5.99  # SZS output start CNFRefutation
% 5.77/5.99  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.77/5.99  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.77/5.99  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.77/5.99  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.77/5.99  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 5.77/5.99  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 5.77/5.99  fof(t13_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 5.77/5.99  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.77/5.99  fof(c_0_8, plain, ![X29, X30]:k3_tarski(k2_tarski(X29,X30))=k2_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 5.77/5.99  fof(c_0_9, plain, ![X27, X28]:k1_enumset1(X27,X27,X28)=k2_tarski(X27,X28), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 5.77/5.99  fof(c_0_10, plain, ![X23, X24]:r1_tarski(X23,k2_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 5.77/5.99  cnf(c_0_11, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 5.77/5.99  cnf(c_0_12, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 5.77/5.99  fof(c_0_13, plain, ![X18, X19, X20]:(~r1_tarski(X18,X19)|~r1_tarski(X19,X20)|r1_tarski(X18,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 5.77/5.99  cnf(c_0_14, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 5.77/5.99  cnf(c_0_15, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 5.77/5.99  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 5.77/5.99  cnf(c_0_17, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 5.77/5.99  cnf(c_0_18, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 5.77/5.99  fof(c_0_19, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 5.77/5.99  fof(c_0_20, plain, ![X31, X32, X33]:(k2_zfmisc_1(k2_xboole_0(X31,X32),X33)=k2_xboole_0(k2_zfmisc_1(X31,X33),k2_zfmisc_1(X32,X33))&k2_zfmisc_1(X33,k2_xboole_0(X31,X32))=k2_xboole_0(k2_zfmisc_1(X33,X31),k2_zfmisc_1(X33,X32))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 5.77/5.99  fof(c_0_21, plain, ![X14, X15, X16, X17]:(~r1_tarski(X14,X15)|~r1_tarski(X16,X17)|r1_tarski(k2_xboole_0(X14,X16),k2_xboole_0(X15,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).
% 5.77/5.99  cnf(c_0_22, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 5.77/5.99  cnf(c_0_23, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 5.77/5.99  cnf(c_0_24, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.77/5.99  cnf(c_0_25, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 5.77/5.99  fof(c_0_26, plain, ![X25, X26]:k2_tarski(X25,X26)=k2_tarski(X26,X25), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 5.77/5.99  cnf(c_0_27, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 5.77/5.99  cnf(c_0_28, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k1_enumset1(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0),X1)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 5.77/5.99  cnf(c_0_29, plain, (k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X3)))=k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_15]), c_0_15])).
% 5.77/5.99  cnf(c_0_30, negated_conjecture, (r1_tarski(esk1_0,k3_tarski(k1_enumset1(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0),X1)))), inference(spm,[status(thm)],[c_0_22, c_0_25])).
% 5.77/5.99  cnf(c_0_31, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 5.77/5.99  cnf(c_0_32, plain, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),k3_tarski(k1_enumset1(X2,X2,X4)))|~r1_tarski(X3,X4)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_15]), c_0_15])).
% 5.77/5.99  cnf(c_0_33, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1))))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 5.77/5.99  cnf(c_0_34, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(esk4_0,esk4_0,X1))))), inference(spm,[status(thm)],[c_0_30, c_0_29])).
% 5.77/5.99  cnf(c_0_35, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_12]), c_0_12])).
% 5.77/5.99  cnf(c_0_36, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,esk2_0)),k3_tarski(k1_enumset1(X2,X2,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X3))))))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 5.77/5.99  cnf(c_0_37, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0))))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 5.77/5.99  cnf(c_0_38, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.77/5.99  cnf(c_0_39, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 5.77/5.99  cnf(c_0_40, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k3_tarski(k1_enumset1(k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0))),k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0))),k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X2))))))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 5.77/5.99  cnf(c_0_41, plain, (k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X2)),X3)=k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_15]), c_0_15])).
% 5.77/5.99  cnf(c_0_42, negated_conjecture, (~r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k1_enumset1(esk3_0,esk3_0,esk5_0)),k3_tarski(k1_enumset1(esk4_0,esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_15]), c_0_15]), c_0_15])).
% 5.77/5.99  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_35]), c_0_42]), ['proof']).
% 5.77/5.99  # SZS output end CNFRefutation
% 5.77/5.99  # Proof object total steps             : 44
% 5.77/5.99  # Proof object clause steps            : 27
% 5.77/5.99  # Proof object formula steps           : 17
% 5.77/5.99  # Proof object conjectures             : 15
% 5.77/5.99  # Proof object clause conjectures      : 12
% 5.77/5.99  # Proof object formula conjectures     : 3
% 5.77/5.99  # Proof object initial clauses used    : 11
% 5.77/5.99  # Proof object initial formulas used   : 8
% 5.77/5.99  # Proof object generating inferences   : 9
% 5.77/5.99  # Proof object simplifying inferences  : 15
% 5.77/5.99  # Training examples: 0 positive, 0 negative
% 5.77/5.99  # Parsed axioms                        : 12
% 5.77/5.99  # Removed by relevancy pruning/SinE    : 0
% 5.77/5.99  # Initial clauses                      : 17
% 5.77/5.99  # Removed in clause preprocessing      : 2
% 5.77/5.99  # Initial clauses in saturation        : 15
% 5.77/5.99  # Processed clauses                    : 21500
% 5.77/5.99  # ...of these trivial                  : 3012
% 5.77/5.99  # ...subsumed                          : 14642
% 5.77/5.99  # ...remaining for further processing  : 3846
% 5.77/5.99  # Other redundant clauses eliminated   : 2
% 5.77/5.99  # Clauses deleted for lack of memory   : 0
% 5.77/5.99  # Backward-subsumed                    : 40
% 5.77/5.99  # Backward-rewritten                   : 139
% 5.77/5.99  # Generated clauses                    : 496761
% 5.77/5.99  # ...of the previous two non-trivial   : 398128
% 5.77/5.99  # Contextual simplify-reflections      : 0
% 5.77/5.99  # Paramodulations                      : 496759
% 5.77/5.99  # Factorizations                       : 0
% 5.77/5.99  # Equation resolutions                 : 2
% 5.77/5.99  # Propositional unsat checks           : 0
% 5.77/5.99  #    Propositional check models        : 0
% 5.77/5.99  #    Propositional check unsatisfiable : 0
% 5.77/5.99  #    Propositional clauses             : 0
% 5.77/5.99  #    Propositional clauses after purity: 0
% 5.77/5.99  #    Propositional unsat core size     : 0
% 5.77/5.99  #    Propositional preprocessing time  : 0.000
% 5.77/5.99  #    Propositional encoding time       : 0.000
% 5.77/5.99  #    Propositional solver time         : 0.000
% 5.77/5.99  #    Success case prop preproc time    : 0.000
% 5.77/5.99  #    Success case prop encoding time   : 0.000
% 5.77/5.99  #    Success case prop solver time     : 0.000
% 5.77/5.99  # Current number of processed clauses  : 3651
% 5.77/5.99  #    Positive orientable unit clauses  : 2451
% 5.77/5.99  #    Positive unorientable unit clauses: 12
% 5.77/5.99  #    Negative unit clauses             : 1
% 5.77/5.99  #    Non-unit-clauses                  : 1187
% 5.77/5.99  # Current number of unprocessed clauses: 376064
% 5.77/5.99  # ...number of literals in the above   : 398480
% 5.77/5.99  # Current number of archived formulas  : 0
% 5.77/5.99  # Current number of archived clauses   : 195
% 5.77/5.99  # Clause-clause subsumption calls (NU) : 791136
% 5.77/5.99  # Rec. Clause-clause subsumption calls : 602502
% 5.77/5.99  # Non-unit clause-clause subsumptions  : 14673
% 5.77/5.99  # Unit Clause-clause subsumption calls : 8517
% 5.77/5.99  # Rewrite failures with RHS unbound    : 0
% 5.77/5.99  # BW rewrite match attempts            : 1527829
% 5.77/5.99  # BW rewrite match successes           : 193
% 5.77/5.99  # Condensation attempts                : 0
% 5.77/5.99  # Condensation successes               : 0
% 5.77/5.99  # Termbank termtop insertions          : 21122864
% 5.77/6.01  
% 5.77/6.01  # -------------------------------------------------
% 5.77/6.01  # User time                : 5.472 s
% 5.77/6.01  # System time              : 0.186 s
% 5.77/6.01  # Total time               : 5.659 s
% 5.77/6.01  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
