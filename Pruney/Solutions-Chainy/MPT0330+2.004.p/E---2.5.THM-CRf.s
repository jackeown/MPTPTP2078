%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:26 EST 2020

% Result     : Theorem 28.63s
% Output     : CNFRefutation 28.63s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 870 expanded)
%              Number of clauses        :   58 ( 419 expanded)
%              Number of leaves         :   14 ( 224 expanded)
%              Depth                    :   17
%              Number of atoms          :  131 (1037 expanded)
%              Number of equality atoms :   42 ( 753 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

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

fof(c_0_14,plain,(
    ! [X42,X43] : k3_tarski(k2_tarski(X42,X43)) = k2_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X40,X41] : k1_enumset1(X40,X40,X41) = k2_tarski(X40,X41) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X25,X26,X27] :
      ( ~ r1_tarski(X25,k2_xboole_0(X26,X27))
      | r1_tarski(k4_xboole_0(X25,X26),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_17,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X36,X37] : k2_xboole_0(X36,X37) = k5_xboole_0(X36,k4_xboole_0(X37,X36)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_20,plain,(
    ! [X31,X32] : r1_tarski(X31,k2_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_21,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X7] : k2_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_26,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_27,plain,(
    ! [X22] : r1_tarski(k1_xboole_0,X22) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_28,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_29])).

fof(c_0_36,plain,(
    ! [X23,X24] : r1_tarski(k4_xboole_0(X23,X24),X23) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_37,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_31,c_0_22])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_40,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(k2_xboole_0(X15,X16),X17)
      | r1_tarski(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_41,plain,(
    ! [X38,X39] : k2_tarski(X38,X39) = k2_tarski(X39,X38) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_42,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_37,c_0_29])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_42])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_50,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X3) ),
    inference(rw,[status(thm)],[c_0_46,c_0_22])).

cnf(c_0_52,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_18]),c_0_18])).

cnf(c_0_53,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_48]),c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k5_xboole_0(X1,k4_xboole_0(X3,X1)),X2) ),
    inference(rw,[status(thm)],[c_0_51,c_0_29])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_52]),c_0_29])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_59,plain,(
    ! [X44,X45,X46] :
      ( k2_zfmisc_1(k2_xboole_0(X44,X45),X46) = k2_xboole_0(k2_zfmisc_1(X44,X46),k2_zfmisc_1(X45,X46))
      & k2_zfmisc_1(X46,k2_xboole_0(X44,X45)) = k2_xboole_0(k2_zfmisc_1(X46,X44),k2_zfmisc_1(X46,X45)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_55])).

fof(c_0_61,plain,(
    ! [X18,X19,X20,X21] :
      ( ~ r1_tarski(X18,X19)
      | ~ r1_tarski(X20,X21)
      | r1_tarski(k2_xboole_0(X18,X20),k2_xboole_0(X19,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k5_xboole_0(X3,k4_xboole_0(X1,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_58]),c_0_33])])).

cnf(c_0_64,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_60]),c_0_33])])).

cnf(c_0_66,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_49])).

cnf(c_0_68,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_22]),c_0_22])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_65]),c_0_49])).

cnf(c_0_70,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),k3_tarski(k1_enumset1(X2,X2,X4)))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_22]),c_0_22])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk2_0,k5_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k4_xboole_0(X1,k2_zfmisc_1(esk5_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_35])).

cnf(c_0_72,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_29]),c_0_29])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k4_xboole_0(X1,k2_zfmisc_1(esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_35])).

cnf(c_0_74,plain,
    ( r1_tarski(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k5_xboole_0(X3,k4_xboole_0(X4,X3)))
    | ~ r1_tarski(X2,X4)
    | ~ r1_tarski(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_29]),c_0_29])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k5_xboole_0(esk6_0,k4_xboole_0(X1,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k5_xboole_0(esk4_0,k4_xboole_0(X1,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_72])).

cnf(c_0_77,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k5_xboole_0(X1,k4_xboole_0(esk2_0,X1)),k5_xboole_0(X2,k4_xboole_0(k2_zfmisc_1(esk5_0,k5_xboole_0(esk6_0,k4_xboole_0(X3,esk6_0))),X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k5_xboole_0(X1,k4_xboole_0(esk4_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_57])).

cnf(c_0_81,plain,
    ( k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X2)),X3) = k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_22]),c_0_22])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k1_enumset1(esk3_0,esk3_0,esk5_0)),k3_tarski(k1_enumset1(esk4_0,esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)),k5_xboole_0(k2_zfmisc_1(esk3_0,k5_xboole_0(X1,k4_xboole_0(esk4_0,X1))),k4_xboole_0(k2_zfmisc_1(esk5_0,k5_xboole_0(esk6_0,k4_xboole_0(X2,esk6_0))),k2_zfmisc_1(esk3_0,k5_xboole_0(X1,k4_xboole_0(esk4_0,X1)))))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_84,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k5_xboole_0(X1,k4_xboole_0(X3,X1)),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_29]),c_0_29])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)),k2_zfmisc_1(k5_xboole_0(esk3_0,k4_xboole_0(esk5_0,esk3_0)),k5_xboole_0(esk4_0,k4_xboole_0(esk6_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_57]),c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.06/0.25  % Computer   : n023.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 09:22:50 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.26  # Version: 2.5pre002
% 0.06/0.26  # No SInE strategy applied
% 0.06/0.26  # Trying AutoSched0 for 299 seconds
% 28.63/28.85  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 28.63/28.85  # and selection function SelectCQArNTNp.
% 28.63/28.85  #
% 28.63/28.85  # Preprocessing time       : 0.012 s
% 28.63/28.85  # Presaturation interreduction done
% 28.63/28.85  
% 28.63/28.85  # Proof found!
% 28.63/28.85  # SZS status Theorem
% 28.63/28.85  # SZS output start CNFRefutation
% 28.63/28.85  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 28.63/28.85  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 28.63/28.85  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 28.63/28.85  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 28.63/28.85  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 28.63/28.85  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 28.63/28.85  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 28.63/28.85  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 28.63/28.85  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 28.63/28.85  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 28.63/28.85  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 28.63/28.85  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 28.63/28.85  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 28.63/28.85  fof(t13_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 28.63/28.85  fof(c_0_14, plain, ![X42, X43]:k3_tarski(k2_tarski(X42,X43))=k2_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 28.63/28.85  fof(c_0_15, plain, ![X40, X41]:k1_enumset1(X40,X40,X41)=k2_tarski(X40,X41), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 28.63/28.85  fof(c_0_16, plain, ![X25, X26, X27]:(~r1_tarski(X25,k2_xboole_0(X26,X27))|r1_tarski(k4_xboole_0(X25,X26),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 28.63/28.85  cnf(c_0_17, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 28.63/28.85  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 28.63/28.85  fof(c_0_19, plain, ![X36, X37]:k2_xboole_0(X36,X37)=k5_xboole_0(X36,k4_xboole_0(X37,X36)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 28.63/28.85  fof(c_0_20, plain, ![X31, X32]:r1_tarski(X31,k2_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 28.63/28.85  cnf(c_0_21, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 28.63/28.85  cnf(c_0_22, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 28.63/28.85  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 28.63/28.85  cnf(c_0_24, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 28.63/28.85  fof(c_0_25, plain, ![X7]:k2_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 28.63/28.85  fof(c_0_26, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 28.63/28.85  fof(c_0_27, plain, ![X22]:r1_tarski(k1_xboole_0,X22), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 28.63/28.85  cnf(c_0_28, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 28.63/28.85  cnf(c_0_29, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[c_0_23, c_0_22])).
% 28.63/28.85  cnf(c_0_30, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_24, c_0_22])).
% 28.63/28.85  cnf(c_0_31, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 28.63/28.85  cnf(c_0_32, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 28.63/28.85  cnf(c_0_33, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 28.63/28.85  cnf(c_0_34, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 28.63/28.85  cnf(c_0_35, plain, (r1_tarski(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_30, c_0_29])).
% 28.63/28.85  fof(c_0_36, plain, ![X23, X24]:r1_tarski(k4_xboole_0(X23,X24),X23), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 28.63/28.85  cnf(c_0_37, plain, (k3_tarski(k1_enumset1(X1,X1,X1))=X1), inference(rw,[status(thm)],[c_0_31, c_0_22])).
% 28.63/28.85  cnf(c_0_38, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 28.63/28.85  cnf(c_0_39, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 28.63/28.85  fof(c_0_40, plain, ![X15, X16, X17]:(~r1_tarski(k2_xboole_0(X15,X16),X17)|r1_tarski(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 28.63/28.85  fof(c_0_41, plain, ![X38, X39]:k2_tarski(X38,X39)=k2_tarski(X39,X38), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 28.63/28.85  cnf(c_0_42, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 28.63/28.85  cnf(c_0_43, plain, (k5_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_37, c_0_29])).
% 28.63/28.85  cnf(c_0_44, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 28.63/28.85  fof(c_0_45, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 28.63/28.85  cnf(c_0_46, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 28.63/28.85  cnf(c_0_47, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 28.63/28.85  cnf(c_0_48, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_42])).
% 28.63/28.85  cnf(c_0_49, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 28.63/28.85  fof(c_0_50, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).
% 28.63/28.85  cnf(c_0_51, plain, (r1_tarski(X1,X3)|~r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X3)), inference(rw,[status(thm)],[c_0_46, c_0_22])).
% 28.63/28.85  cnf(c_0_52, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_18]), c_0_18])).
% 28.63/28.85  cnf(c_0_53, plain, (r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_48]), c_0_49])).
% 28.63/28.85  cnf(c_0_54, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 28.63/28.85  cnf(c_0_55, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 28.63/28.85  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~r1_tarski(k5_xboole_0(X1,k4_xboole_0(X3,X1)),X2)), inference(rw,[status(thm)],[c_0_51, c_0_29])).
% 28.63/28.85  cnf(c_0_57, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_52]), c_0_29])).
% 28.63/28.85  cnf(c_0_58, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 28.63/28.85  fof(c_0_59, plain, ![X44, X45, X46]:(k2_zfmisc_1(k2_xboole_0(X44,X45),X46)=k2_xboole_0(k2_zfmisc_1(X44,X46),k2_zfmisc_1(X45,X46))&k2_zfmisc_1(X46,k2_xboole_0(X44,X45))=k2_xboole_0(k2_zfmisc_1(X46,X44),k2_zfmisc_1(X46,X45))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 28.63/28.85  cnf(c_0_60, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_55])).
% 28.63/28.85  fof(c_0_61, plain, ![X18, X19, X20, X21]:(~r1_tarski(X18,X19)|~r1_tarski(X20,X21)|r1_tarski(k2_xboole_0(X18,X20),k2_xboole_0(X19,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).
% 28.63/28.85  cnf(c_0_62, plain, (r1_tarski(X1,X2)|~r1_tarski(k5_xboole_0(X3,k4_xboole_0(X1,X3)),X2)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 28.63/28.85  cnf(c_0_63, negated_conjecture, (k4_xboole_0(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_58]), c_0_33])])).
% 28.63/28.85  cnf(c_0_64, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 28.63/28.85  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_60]), c_0_33])])).
% 28.63/28.85  cnf(c_0_66, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 28.63/28.85  cnf(c_0_67, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_49])).
% 28.63/28.85  cnf(c_0_68, plain, (k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X3)))=k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_22]), c_0_22])).
% 28.63/28.85  cnf(c_0_69, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_65]), c_0_49])).
% 28.63/28.85  cnf(c_0_70, plain, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),k3_tarski(k1_enumset1(X2,X2,X4)))|~r1_tarski(X3,X4)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_22]), c_0_22])).
% 28.63/28.85  cnf(c_0_71, negated_conjecture, (r1_tarski(esk2_0,k5_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k4_xboole_0(X1,k2_zfmisc_1(esk5_0,esk6_0))))), inference(spm,[status(thm)],[c_0_67, c_0_35])).
% 28.63/28.85  cnf(c_0_72, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X2)))=k2_zfmisc_1(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_29]), c_0_29])).
% 28.63/28.85  cnf(c_0_73, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k4_xboole_0(X1,k2_zfmisc_1(esk3_0,esk4_0))))), inference(spm,[status(thm)],[c_0_69, c_0_35])).
% 28.63/28.85  cnf(c_0_74, plain, (r1_tarski(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k5_xboole_0(X3,k4_xboole_0(X4,X3)))|~r1_tarski(X2,X4)|~r1_tarski(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_29]), c_0_29])).
% 28.63/28.85  cnf(c_0_75, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k5_xboole_0(esk6_0,k4_xboole_0(X1,esk6_0))))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 28.63/28.85  cnf(c_0_76, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k5_xboole_0(esk4_0,k4_xboole_0(X1,esk4_0))))), inference(spm,[status(thm)],[c_0_73, c_0_72])).
% 28.63/28.85  cnf(c_0_77, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 28.63/28.85  cnf(c_0_78, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 28.63/28.85  cnf(c_0_79, negated_conjecture, (r1_tarski(k5_xboole_0(X1,k4_xboole_0(esk2_0,X1)),k5_xboole_0(X2,k4_xboole_0(k2_zfmisc_1(esk5_0,k5_xboole_0(esk6_0,k4_xboole_0(X3,esk6_0))),X2)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 28.63/28.85  cnf(c_0_80, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k5_xboole_0(X1,k4_xboole_0(esk4_0,X1))))), inference(spm,[status(thm)],[c_0_76, c_0_57])).
% 28.63/28.85  cnf(c_0_81, plain, (k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X2)),X3)=k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_22]), c_0_22])).
% 28.63/28.85  cnf(c_0_82, negated_conjecture, (~r1_tarski(k3_tarski(k1_enumset1(esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k1_enumset1(esk3_0,esk3_0,esk5_0)),k3_tarski(k1_enumset1(esk4_0,esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_22]), c_0_22]), c_0_22])).
% 28.63/28.85  cnf(c_0_83, negated_conjecture, (r1_tarski(k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)),k5_xboole_0(k2_zfmisc_1(esk3_0,k5_xboole_0(X1,k4_xboole_0(esk4_0,X1))),k4_xboole_0(k2_zfmisc_1(esk5_0,k5_xboole_0(esk6_0,k4_xboole_0(X2,esk6_0))),k2_zfmisc_1(esk3_0,k5_xboole_0(X1,k4_xboole_0(esk4_0,X1))))))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 28.63/28.85  cnf(c_0_84, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X1,X2)))=k2_zfmisc_1(k5_xboole_0(X1,k4_xboole_0(X3,X1)),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_29]), c_0_29])).
% 28.63/28.85  cnf(c_0_85, negated_conjecture, (~r1_tarski(k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)),k2_zfmisc_1(k5_xboole_0(esk3_0,k4_xboole_0(esk5_0,esk3_0)),k5_xboole_0(esk4_0,k4_xboole_0(esk6_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_29]), c_0_29]), c_0_29])).
% 28.63/28.85  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_57]), c_0_85]), ['proof']).
% 28.63/28.85  # SZS output end CNFRefutation
% 28.63/28.85  # Proof object total steps             : 87
% 28.63/28.85  # Proof object clause steps            : 58
% 28.63/28.85  # Proof object formula steps           : 29
% 28.63/28.85  # Proof object conjectures             : 22
% 28.63/28.85  # Proof object clause conjectures      : 19
% 28.63/28.85  # Proof object formula conjectures     : 3
% 28.63/28.85  # Proof object initial clauses used    : 17
% 28.63/28.85  # Proof object initial formulas used   : 14
% 28.63/28.85  # Proof object generating inferences   : 21
% 28.63/28.85  # Proof object simplifying inferences  : 41
% 28.63/28.85  # Training examples: 0 positive, 0 negative
% 28.63/28.85  # Parsed axioms                        : 18
% 28.63/28.85  # Removed by relevancy pruning/SinE    : 0
% 28.63/28.85  # Initial clauses                      : 24
% 28.63/28.85  # Removed in clause preprocessing      : 2
% 28.63/28.85  # Initial clauses in saturation        : 22
% 28.63/28.85  # Processed clauses                    : 39221
% 28.63/28.85  # ...of these trivial                  : 2717
% 28.63/28.85  # ...subsumed                          : 24653
% 28.63/28.85  # ...remaining for further processing  : 11851
% 28.63/28.85  # Other redundant clauses eliminated   : 2
% 28.63/28.85  # Clauses deleted for lack of memory   : 0
% 28.63/28.85  # Backward-subsumed                    : 161
% 28.63/28.85  # Backward-rewritten                   : 1381
% 28.63/28.85  # Generated clauses                    : 2035723
% 28.63/28.85  # ...of the previous two non-trivial   : 1637329
% 28.63/28.85  # Contextual simplify-reflections      : 0
% 28.63/28.85  # Paramodulations                      : 2035721
% 28.63/28.85  # Factorizations                       : 0
% 28.63/28.85  # Equation resolutions                 : 2
% 28.63/28.85  # Propositional unsat checks           : 0
% 28.63/28.85  #    Propositional check models        : 0
% 28.63/28.85  #    Propositional check unsatisfiable : 0
% 28.63/28.85  #    Propositional clauses             : 0
% 28.63/28.85  #    Propositional clauses after purity: 0
% 28.63/28.85  #    Propositional unsat core size     : 0
% 28.63/28.85  #    Propositional preprocessing time  : 0.000
% 28.63/28.85  #    Propositional encoding time       : 0.000
% 28.63/28.85  #    Propositional solver time         : 0.000
% 28.63/28.85  #    Success case prop preproc time    : 0.000
% 28.63/28.85  #    Success case prop encoding time   : 0.000
% 28.63/28.85  #    Success case prop solver time     : 0.000
% 28.63/28.85  # Current number of processed clauses  : 10286
% 28.63/28.85  #    Positive orientable unit clauses  : 7718
% 28.63/28.85  #    Positive unorientable unit clauses: 2
% 28.63/28.85  #    Negative unit clauses             : 1
% 28.63/28.85  #    Non-unit-clauses                  : 2565
% 28.63/28.85  # Current number of unprocessed clauses: 1594676
% 28.63/28.85  # ...number of literals in the above   : 1663370
% 28.63/28.85  # Current number of archived formulas  : 0
% 28.63/28.85  # Current number of archived clauses   : 1565
% 28.63/28.85  # Clause-clause subsumption calls (NU) : 673706
% 28.63/28.85  # Rec. Clause-clause subsumption calls : 586218
% 28.63/28.85  # Non-unit clause-clause subsumptions  : 24808
% 28.63/28.85  # Unit Clause-clause subsumption calls : 42628
% 28.63/28.85  # Rewrite failures with RHS unbound    : 0
% 28.63/28.85  # BW rewrite match attempts            : 3855382
% 28.63/28.85  # BW rewrite match successes           : 1233
% 28.63/28.85  # Condensation attempts                : 0
% 28.63/28.85  # Condensation successes               : 0
% 28.63/28.85  # Termbank termtop insertions          : 97946701
% 28.69/28.94  
% 28.69/28.94  # -------------------------------------------------
% 28.69/28.94  # User time                : 27.590 s
% 28.69/28.94  # System time              : 1.080 s
% 28.69/28.94  # Total time               : 28.670 s
% 28.69/28.94  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
