%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:12 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 546 expanded)
%              Number of clauses        :   45 ( 257 expanded)
%              Number of leaves         :   14 ( 144 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 769 expanded)
%              Number of equality atoms :   46 ( 488 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t86_zfmisc_1,conjecture,(
    ! [X1,X2] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X2,X1))),k1_zfmisc_1(k5_xboole_0(X1,X2))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(c_0_14,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_19,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_20,plain,(
    ! [X17,X18] : r1_tarski(k4_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X2,X1))),k1_zfmisc_1(k5_xboole_0(X1,X2))) ),
    inference(assume_negation,[status(cth)],[t86_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X28,X29] : k3_tarski(k2_tarski(X28,X29)) = k2_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_24,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,negated_conjecture,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(esk1_0,esk2_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk1_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_29,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X1))) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_27,c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(esk1_0,esk2_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk1_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_37,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,X22)
      | ~ r1_tarski(X23,X22)
      | r1_tarski(k2_xboole_0(X21,X23),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_25])).

fof(c_0_41,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_42,plain,(
    ! [X24,X25] : k2_tarski(X24,X25) = k2_tarski(X25,X24) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k1_enumset1(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_44,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_25])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X1)) = k5_xboole_0(X1,k3_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_39])).

cnf(c_0_47,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_33])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k1_enumset1(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_38])).

cnf(c_0_51,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_36])).

fof(c_0_52,plain,(
    ! [X30,X31] :
      ( ~ r1_tarski(X30,X31)
      | r1_tarski(k1_zfmisc_1(X30),k1_zfmisc_1(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

fof(c_0_53,plain,(
    ! [X12,X13,X14] : k5_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(X14,X13)) = k3_xboole_0(k5_xboole_0(X12,X14),X13) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k5_xboole_0(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_45]),c_0_47])])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,X2) = k3_tarski(k1_enumset1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_36]),c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_57,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_30]),c_0_30])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))
    | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_24])).

cnf(c_0_61,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_54]),c_0_46]),c_0_54]),c_0_55])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))
    | ~ r1_tarski(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_38])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,X1)) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_38]),c_0_63])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_38])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,esk2_0))
    | ~ r1_tarski(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_59])).

cnf(c_0_69,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),k5_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])])).

cnf(c_0_72,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_38])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.045 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.43  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.43  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.43  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.43  fof(t86_zfmisc_1, conjecture, ![X1, X2]:r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X2,X1))),k1_zfmisc_1(k5_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 0.19/0.43  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.43  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.43  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.19/0.43  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.19/0.43  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.43  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 0.19/0.43  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 0.19/0.43  fof(c_0_14, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.43  fof(c_0_15, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.43  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.43  fof(c_0_18, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.43  fof(c_0_19, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.43  fof(c_0_20, plain, ![X17, X18]:r1_tarski(k4_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.43  fof(c_0_21, negated_conjecture, ~(![X1, X2]:r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X2,X1))),k1_zfmisc_1(k5_xboole_0(X1,X2)))), inference(assume_negation,[status(cth)],[t86_zfmisc_1])).
% 0.19/0.43  fof(c_0_22, plain, ![X28, X29]:k3_tarski(k2_tarski(X28,X29))=k2_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.43  fof(c_0_23, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.43  cnf(c_0_24, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17])).
% 0.19/0.43  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.43  cnf(c_0_26, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.43  cnf(c_0_27, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.43  fof(c_0_28, negated_conjecture, ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(esk1_0,esk2_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk1_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.19/0.43  cnf(c_0_29, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.43  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.43  fof(c_0_31, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.43  cnf(c_0_32, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X1)))=X1|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.43  cnf(c_0_33, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_26])).
% 0.19/0.43  cnf(c_0_34, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_27, c_0_17])).
% 0.19/0.43  cnf(c_0_35, negated_conjecture, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(esk1_0,esk2_0)),k1_zfmisc_1(k4_xboole_0(esk2_0,esk1_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.43  cnf(c_0_36, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.43  fof(c_0_37, plain, ![X21, X22, X23]:(~r1_tarski(X21,X22)|~r1_tarski(X23,X22)|r1_tarski(k2_xboole_0(X21,X23),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.19/0.43  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.43  cnf(c_0_39, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X1)))=X1), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.43  cnf(c_0_40, plain, (r1_tarski(k5_xboole_0(X1,X1),X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_25])).
% 0.19/0.43  fof(c_0_41, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.19/0.43  fof(c_0_42, plain, ![X24, X25]:k2_tarski(X24,X25)=k2_tarski(X25,X24), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.43  cnf(c_0_43, negated_conjecture, (~r1_tarski(k3_tarski(k1_enumset1(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk1_0))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_17]), c_0_17]), c_0_17])).
% 0.19/0.43  cnf(c_0_44, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.43  cnf(c_0_45, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_25])).
% 0.19/0.43  cnf(c_0_46, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X1))=k5_xboole_0(X1,k3_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_24, c_0_39])).
% 0.19/0.43  cnf(c_0_47, plain, (r1_tarski(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_40, c_0_33])).
% 0.19/0.43  cnf(c_0_48, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.43  cnf(c_0_49, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.43  cnf(c_0_50, negated_conjecture, (~r1_tarski(k3_tarski(k1_enumset1(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[c_0_43, c_0_38])).
% 0.19/0.43  cnf(c_0_51, plain, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_44, c_0_36])).
% 0.19/0.43  fof(c_0_52, plain, ![X30, X31]:(~r1_tarski(X30,X31)|r1_tarski(k1_zfmisc_1(X30),k1_zfmisc_1(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 0.19/0.43  fof(c_0_53, plain, ![X12, X13, X14]:k5_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(X14,X13))=k3_xboole_0(k5_xboole_0(X12,X14),X13), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 0.19/0.43  cnf(c_0_54, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k5_xboole_0(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.19/0.43  cnf(c_0_55, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_45]), c_0_47])])).
% 0.19/0.43  cnf(c_0_56, plain, (k5_xboole_0(X1,X2)=k3_tarski(k1_enumset1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_36]), c_0_17]), c_0_17]), c_0_17])).
% 0.19/0.43  cnf(c_0_57, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_30]), c_0_30])).
% 0.19/0.43  cnf(c_0_58, negated_conjecture, (~r1_tarski(k1_zfmisc_1(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))|~r1_tarski(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.43  cnf(c_0_59, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.43  cnf(c_0_60, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_34, c_0_24])).
% 0.19/0.43  cnf(c_0_61, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.43  cnf(c_0_62, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_54]), c_0_46]), c_0_54]), c_0_55])).
% 0.19/0.43  cnf(c_0_63, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_56])).
% 0.19/0.43  cnf(c_0_64, negated_conjecture, (~r1_tarski(k1_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k5_xboole_0(esk1_0,esk2_0)))|~r1_tarski(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.43  cnf(c_0_65, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_60, c_0_38])).
% 0.19/0.43  cnf(c_0_66, plain, (k3_xboole_0(X1,k5_xboole_0(X2,X1))=k5_xboole_0(X1,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_38]), c_0_63])).
% 0.19/0.43  cnf(c_0_67, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(X1,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_38])).
% 0.19/0.43  cnf(c_0_68, negated_conjecture, (~r1_tarski(k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,esk2_0))|~r1_tarski(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_64, c_0_59])).
% 0.19/0.43  cnf(c_0_69, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),k5_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.43  cnf(c_0_70, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_65, c_0_67])).
% 0.19/0.43  cnf(c_0_71, negated_conjecture, (~r1_tarski(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69])])).
% 0.19/0.43  cnf(c_0_72, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_70, c_0_38])).
% 0.19/0.43  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72])]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 74
% 0.19/0.43  # Proof object clause steps            : 45
% 0.19/0.43  # Proof object formula steps           : 29
% 0.19/0.43  # Proof object conjectures             : 11
% 0.19/0.43  # Proof object clause conjectures      : 8
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 14
% 0.19/0.43  # Proof object initial formulas used   : 14
% 0.19/0.43  # Proof object generating inferences   : 20
% 0.19/0.43  # Proof object simplifying inferences  : 32
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 14
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 16
% 0.19/0.43  # Removed in clause preprocessing      : 3
% 0.19/0.43  # Initial clauses in saturation        : 13
% 0.19/0.43  # Processed clauses                    : 392
% 0.19/0.43  # ...of these trivial                  : 30
% 0.19/0.43  # ...subsumed                          : 215
% 0.19/0.43  # ...remaining for further processing  : 147
% 0.19/0.43  # Other redundant clauses eliminated   : 2
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 0
% 0.19/0.43  # Backward-rewritten                   : 16
% 0.19/0.43  # Generated clauses                    : 1948
% 0.19/0.43  # ...of the previous two non-trivial   : 1626
% 0.19/0.43  # Contextual simplify-reflections      : 0
% 0.19/0.43  # Paramodulations                      : 1946
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 2
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 117
% 0.19/0.43  #    Positive orientable unit clauses  : 31
% 0.19/0.43  #    Positive unorientable unit clauses: 3
% 0.19/0.43  #    Negative unit clauses             : 3
% 0.19/0.43  #    Non-unit-clauses                  : 80
% 0.19/0.43  # Current number of unprocessed clauses: 1241
% 0.19/0.43  # ...number of literals in the above   : 2594
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 31
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 1859
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 1809
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 208
% 0.19/0.43  # Unit Clause-clause subsumption calls : 48
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 115
% 0.19/0.43  # BW rewrite match successes           : 44
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 22486
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.083 s
% 0.19/0.43  # System time              : 0.009 s
% 0.19/0.43  # Total time               : 0.092 s
% 0.19/0.43  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
