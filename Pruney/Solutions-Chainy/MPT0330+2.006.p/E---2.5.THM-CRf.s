%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:26 EST 2020

% Result     : Theorem 8.46s
% Output     : CNFRefutation 8.46s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 234 expanded)
%              Number of clauses        :   36 ( 109 expanded)
%              Number of leaves         :   10 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :   90 ( 297 expanded)
%              Number of equality atoms :   19 ( 177 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

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

fof(c_0_10,plain,(
    ! [X28,X29] : k3_tarski(k2_tarski(X28,X29)) = k2_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X22,X23] : r1_tarski(X22,k2_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_13,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X24,X25] : k2_tarski(X24,X25) = k2_tarski(X25,X24) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,k2_xboole_0(X17,X18))
      | r1_tarski(k4_xboole_0(X16,X17),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_22,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_23,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_14]),c_0_14])).

fof(c_0_26,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(k4_xboole_0(X19,X20),X21)
      | r1_tarski(X19,k2_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk5_0,esk6_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_31,c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,X1),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_36,plain,(
    ! [X30,X31,X32] :
      ( k2_zfmisc_1(k2_xboole_0(X30,X31),X32) = k2_xboole_0(k2_zfmisc_1(X30,X32),k2_zfmisc_1(X31,X32))
      & k2_zfmisc_1(X32,k2_xboole_0(X30,X31)) = k2_xboole_0(k2_zfmisc_1(X32,X30),k2_zfmisc_1(X32,X31)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_38,plain,(
    ! [X9,X10,X11,X12] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X11,X12)
      | r1_tarski(k2_xboole_0(X9,X11),k2_xboole_0(X10,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k1_enumset1(X1,X1,k2_zfmisc_1(esk5_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_37])).

cnf(c_0_42,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k1_enumset1(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0),X1))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_19]),c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,X1),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_33])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),k3_tarski(k1_enumset1(X2,X2,X4)))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_19]),c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk1_0,k3_tarski(k1_enumset1(X1,X1,k2_zfmisc_1(esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,esk2_0)),k3_tarski(k1_enumset1(X2,X2,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X3))))))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_44])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k3_tarski(k1_enumset1(k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0))),k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0))),k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X2)))))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,plain,
    ( k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X2)),X3) = k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_19]),c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k1_enumset1(esk3_0,esk3_0,esk5_0)),k3_tarski(k1_enumset1(esk4_0,esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_25]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:46:38 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 8.46/8.70  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 8.46/8.70  # and selection function SelectCQArNTNp.
% 8.46/8.70  #
% 8.46/8.70  # Preprocessing time       : 0.027 s
% 8.46/8.70  # Presaturation interreduction done
% 8.46/8.70  
% 8.46/8.70  # Proof found!
% 8.46/8.70  # SZS status Theorem
% 8.46/8.70  # SZS output start CNFRefutation
% 8.46/8.70  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.46/8.70  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 8.46/8.70  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.46/8.70  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.46/8.70  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 8.46/8.70  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 8.46/8.70  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.46/8.70  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 8.46/8.70  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 8.46/8.70  fof(t13_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 8.46/8.70  fof(c_0_10, plain, ![X28, X29]:k3_tarski(k2_tarski(X28,X29))=k2_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 8.46/8.70  fof(c_0_11, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 8.46/8.70  fof(c_0_12, plain, ![X22, X23]:r1_tarski(X22,k2_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 8.46/8.70  cnf(c_0_13, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 8.46/8.70  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 8.46/8.70  fof(c_0_15, plain, ![X24, X25]:k2_tarski(X24,X25)=k2_tarski(X25,X24), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 8.46/8.70  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 8.46/8.70  fof(c_0_17, plain, ![X16, X17, X18]:(~r1_tarski(X16,k2_xboole_0(X17,X18))|r1_tarski(k4_xboole_0(X16,X17),X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 8.46/8.70  cnf(c_0_18, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 8.46/8.70  cnf(c_0_19, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 8.46/8.70  cnf(c_0_20, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 8.46/8.70  fof(c_0_21, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 8.46/8.70  fof(c_0_22, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 8.46/8.70  cnf(c_0_23, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 8.46/8.70  cnf(c_0_24, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 8.46/8.70  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_14]), c_0_14])).
% 8.46/8.70  fof(c_0_26, plain, ![X19, X20, X21]:(~r1_tarski(k4_xboole_0(X19,X20),X21)|r1_tarski(X19,k2_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 8.46/8.70  cnf(c_0_27, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 8.46/8.70  cnf(c_0_28, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 8.46/8.70  cnf(c_0_29, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_23, c_0_19])).
% 8.46/8.70  cnf(c_0_30, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X1)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 8.46/8.70  cnf(c_0_31, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 8.46/8.70  cnf(c_0_32, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk5_0,esk6_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 8.46/8.70  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 8.46/8.70  cnf(c_0_34, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_31, c_0_19])).
% 8.46/8.70  cnf(c_0_35, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,X1),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 8.46/8.70  fof(c_0_36, plain, ![X30, X31, X32]:(k2_zfmisc_1(k2_xboole_0(X30,X31),X32)=k2_xboole_0(k2_zfmisc_1(X30,X32),k2_zfmisc_1(X31,X32))&k2_zfmisc_1(X32,k2_xboole_0(X30,X31))=k2_xboole_0(k2_zfmisc_1(X32,X30),k2_zfmisc_1(X32,X31))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 8.46/8.70  cnf(c_0_37, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 8.46/8.70  fof(c_0_38, plain, ![X9, X10, X11, X12]:(~r1_tarski(X9,X10)|~r1_tarski(X11,X12)|r1_tarski(k2_xboole_0(X9,X11),k2_xboole_0(X10,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).
% 8.46/8.70  cnf(c_0_39, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k1_enumset1(X1,X1,k2_zfmisc_1(esk5_0,esk6_0))))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 8.46/8.70  cnf(c_0_40, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 8.46/8.70  cnf(c_0_41, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0))|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_27, c_0_37])).
% 8.46/8.70  cnf(c_0_42, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 8.46/8.70  cnf(c_0_43, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k1_enumset1(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk5_0,esk6_0),X1)))), inference(spm,[status(thm)],[c_0_39, c_0_25])).
% 8.46/8.70  cnf(c_0_44, plain, (k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X3)))=k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_19]), c_0_19])).
% 8.46/8.70  cnf(c_0_45, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,X1),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_41, c_0_33])).
% 8.46/8.70  cnf(c_0_46, plain, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),k3_tarski(k1_enumset1(X2,X2,X4)))|~r1_tarski(X3,X4)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_19]), c_0_19])).
% 8.46/8.70  cnf(c_0_47, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X1))))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 8.46/8.70  cnf(c_0_48, negated_conjecture, (r1_tarski(esk1_0,k3_tarski(k1_enumset1(X1,X1,k2_zfmisc_1(esk3_0,esk4_0))))), inference(spm,[status(thm)],[c_0_34, c_0_45])).
% 8.46/8.70  cnf(c_0_49, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,esk2_0)),k3_tarski(k1_enumset1(X2,X2,k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X3))))))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 8.46/8.70  cnf(c_0_50, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0))))), inference(spm,[status(thm)],[c_0_48, c_0_44])).
% 8.46/8.70  cnf(c_0_51, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 8.46/8.70  cnf(c_0_52, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 8.46/8.70  cnf(c_0_53, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k3_tarski(k1_enumset1(k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0))),k2_zfmisc_1(esk3_0,k3_tarski(k1_enumset1(X1,X1,esk4_0))),k2_zfmisc_1(esk5_0,k3_tarski(k1_enumset1(esk6_0,esk6_0,X2))))))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 8.46/8.70  cnf(c_0_54, plain, (k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X2)),X3)=k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_19]), c_0_19])).
% 8.46/8.70  cnf(c_0_55, negated_conjecture, (~r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k1_enumset1(esk3_0,esk3_0,esk5_0)),k3_tarski(k1_enumset1(esk4_0,esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_19]), c_0_19]), c_0_19])).
% 8.46/8.70  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_25]), c_0_55]), ['proof']).
% 8.46/8.70  # SZS output end CNFRefutation
% 8.46/8.70  # Proof object total steps             : 57
% 8.46/8.70  # Proof object clause steps            : 36
% 8.46/8.70  # Proof object formula steps           : 21
% 8.46/8.70  # Proof object conjectures             : 19
% 8.46/8.70  # Proof object clause conjectures      : 16
% 8.46/8.70  # Proof object formula conjectures     : 3
% 8.46/8.70  # Proof object initial clauses used    : 13
% 8.46/8.70  # Proof object initial formulas used   : 10
% 8.46/8.70  # Proof object generating inferences   : 14
% 8.46/8.70  # Proof object simplifying inferences  : 17
% 8.46/8.70  # Training examples: 0 positive, 0 negative
% 8.46/8.70  # Parsed axioms                        : 11
% 8.46/8.70  # Removed by relevancy pruning/SinE    : 0
% 8.46/8.70  # Initial clauses                      : 16
% 8.46/8.70  # Removed in clause preprocessing      : 2
% 8.46/8.70  # Initial clauses in saturation        : 14
% 8.46/8.70  # Processed clauses                    : 24811
% 8.46/8.70  # ...of these trivial                  : 1541
% 8.46/8.70  # ...subsumed                          : 18526
% 8.46/8.70  # ...remaining for further processing  : 4744
% 8.46/8.70  # Other redundant clauses eliminated   : 2
% 8.46/8.70  # Clauses deleted for lack of memory   : 0
% 8.46/8.70  # Backward-subsumed                    : 123
% 8.46/8.70  # Backward-rewritten                   : 334
% 8.46/8.70  # Generated clauses                    : 718179
% 8.46/8.70  # ...of the previous two non-trivial   : 605706
% 8.46/8.70  # Contextual simplify-reflections      : 0
% 8.46/8.70  # Paramodulations                      : 718177
% 8.46/8.70  # Factorizations                       : 0
% 8.46/8.70  # Equation resolutions                 : 2
% 8.46/8.70  # Propositional unsat checks           : 0
% 8.46/8.70  #    Propositional check models        : 0
% 8.46/8.70  #    Propositional check unsatisfiable : 0
% 8.46/8.70  #    Propositional clauses             : 0
% 8.46/8.70  #    Propositional clauses after purity: 0
% 8.46/8.70  #    Propositional unsat core size     : 0
% 8.46/8.70  #    Propositional preprocessing time  : 0.000
% 8.46/8.70  #    Propositional encoding time       : 0.000
% 8.46/8.70  #    Propositional solver time         : 0.000
% 8.46/8.70  #    Success case prop preproc time    : 0.000
% 8.46/8.70  #    Success case prop encoding time   : 0.000
% 8.46/8.70  #    Success case prop solver time     : 0.000
% 8.46/8.70  # Current number of processed clauses  : 4272
% 8.46/8.70  #    Positive orientable unit clauses  : 2778
% 8.46/8.70  #    Positive unorientable unit clauses: 13
% 8.46/8.70  #    Negative unit clauses             : 1
% 8.46/8.70  #    Non-unit-clauses                  : 1480
% 8.46/8.70  # Current number of unprocessed clauses: 579962
% 8.46/8.70  # ...number of literals in the above   : 600568
% 8.46/8.70  # Current number of archived formulas  : 0
% 8.46/8.70  # Current number of archived clauses   : 472
% 8.46/8.70  # Clause-clause subsumption calls (NU) : 1293774
% 8.46/8.70  # Rec. Clause-clause subsumption calls : 1022081
% 8.46/8.70  # Non-unit clause-clause subsumptions  : 18262
% 8.46/8.70  # Unit Clause-clause subsumption calls : 9278
% 8.46/8.70  # Rewrite failures with RHS unbound    : 295
% 8.46/8.70  # BW rewrite match attempts            : 973101
% 8.46/8.70  # BW rewrite match successes           : 377
% 8.46/8.70  # Condensation attempts                : 0
% 8.46/8.70  # Condensation successes               : 0
% 8.46/8.70  # Termbank termtop insertions          : 28048436
% 8.55/8.73  
% 8.55/8.73  # -------------------------------------------------
% 8.55/8.73  # User time                : 8.059 s
% 8.55/8.73  # System time              : 0.338 s
% 8.55/8.73  # Total time               : 8.397 s
% 8.55/8.73  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
