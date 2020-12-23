%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 784 expanded)
%              Number of clauses        :   52 ( 344 expanded)
%              Number of leaves         :   11 ( 197 expanded)
%              Depth                    :   22
%              Number of atoms          :  129 (1941 expanded)
%              Number of equality atoms :   72 (1362 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X22,X23,X24] :
      ( k2_zfmisc_1(k2_xboole_0(X22,X23),X24) = k2_xboole_0(k2_zfmisc_1(X22,X24),k2_zfmisc_1(X23,X24))
      & k2_zfmisc_1(X24,k2_xboole_0(X22,X23)) = k2_xboole_0(k2_zfmisc_1(X24,X22),k2_zfmisc_1(X24,X23)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

fof(c_0_13,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k2_zfmisc_1(esk3_0,esk4_0)
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & ( esk1_0 != esk3_0
      | esk2_0 != esk4_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_15,plain,(
    ! [X15,X16] : k3_xboole_0(X15,k2_xboole_0(X15,X16)) = X15 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,X1)) = k2_zfmisc_1(esk3_0,k2_xboole_0(X1,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

fof(c_0_22,plain,(
    ! [X25,X26,X27,X28] : k2_zfmisc_1(k3_xboole_0(X25,X26),k3_xboole_0(X27,X28)) = k3_xboole_0(k2_zfmisc_1(X25,X27),k2_zfmisc_1(X26,X28)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k2_xboole_0(X11,X12) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k2_xboole_0(X1,esk4_0))) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X20,X19),k2_zfmisc_1(X21,X19))
        | X19 = k1_xboole_0
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(k2_zfmisc_1(X19,X20),k2_zfmisc_1(X19,X21))
        | X19 = k1_xboole_0
        | r1_tarski(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_28,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k2_xboole_0(esk4_0,esk4_0)) = k2_zfmisc_1(esk1_0,k2_xboole_0(esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_16])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,k2_xboole_0(X1,esk4_0))) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k2_xboole_0(esk2_0,esk2_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_17]),c_0_30])])).

cnf(c_0_34,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,esk2_0),X1)
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

fof(c_0_39,plain,(
    ! [X17,X18] : r1_tarski(X17,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(X1,k3_xboole_0(esk1_0,esk3_0))
    | ~ r1_tarski(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

fof(c_0_41,plain,(
    ! [X13,X14] : r1_tarski(k3_xboole_0(X13,X14),X13) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_30])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk1_0,k3_xboole_0(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_30])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_45]),c_0_46])])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,X1)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,k2_xboole_0(X1,esk4_0))) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_48])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk2_0,k3_xboole_0(esk2_0,k2_xboole_0(X1,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_30])])).

cnf(c_0_53,negated_conjecture,
    ( k2_zfmisc_1(k2_xboole_0(esk1_0,esk3_0),esk2_0) = k2_zfmisc_1(esk3_0,k2_xboole_0(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_xboole_0(X1,esk4_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_52]),c_0_46])])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk1_0,esk3_0),X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,k2_xboole_0(esk2_0,esk4_0)),k2_zfmisc_1(X1,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_53]),c_0_37])).

fof(c_0_56,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_xboole_0(esk4_0,X1)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_18])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk1_0,esk3_0),X1)
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(X1,esk2_0))
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_29]),c_0_17])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( k3_xboole_0(esk2_0,X1) = esk2_0
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_29])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk1_0,esk3_0),esk1_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_30])).

cnf(c_0_62,negated_conjecture,
    ( k3_xboole_0(X1,esk2_0) = esk2_0
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_64,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk3_0) = esk1_0
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_61]),c_0_44])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( esk3_0 = esk1_0
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_59]),c_0_48])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_30])).

cnf(c_0_68,negated_conjecture,
    ( esk3_0 = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_69,negated_conjecture,
    ( esk1_0 != esk3_0
    | esk2_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_70,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk4_0) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_17,c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( esk4_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_68])])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_70]),c_0_34])).

cnf(c_0_73,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_67]),c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_30]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:22:14 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.20/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.050 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.20/0.41  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 0.20/0.41  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.41  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.20/0.41  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.41  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 0.20/0.41  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.41  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.41  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.41  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 0.20/0.41  fof(c_0_12, plain, ![X22, X23, X24]:(k2_zfmisc_1(k2_xboole_0(X22,X23),X24)=k2_xboole_0(k2_zfmisc_1(X22,X24),k2_zfmisc_1(X23,X24))&k2_zfmisc_1(X24,k2_xboole_0(X22,X23))=k2_xboole_0(k2_zfmisc_1(X24,X22),k2_zfmisc_1(X24,X23))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 0.20/0.41  fof(c_0_13, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k2_zfmisc_1(esk3_0,esk4_0)&((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&(esk1_0!=esk3_0|esk2_0!=esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.20/0.41  fof(c_0_14, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.41  fof(c_0_15, plain, ![X15, X16]:k3_xboole_0(X15,k2_xboole_0(X15,X16))=X15, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.20/0.41  cnf(c_0_16, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_17, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k2_zfmisc_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  fof(c_0_19, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  cnf(c_0_20, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_21, negated_conjecture, (k2_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,X1))=k2_zfmisc_1(esk3_0,k2_xboole_0(X1,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.20/0.41  fof(c_0_22, plain, ![X25, X26, X27, X28]:k2_zfmisc_1(k3_xboole_0(X25,X26),k3_xboole_0(X27,X28))=k3_xboole_0(k2_zfmisc_1(X25,X27),k2_zfmisc_1(X26,X28)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.20/0.41  fof(c_0_23, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k2_xboole_0(X11,X12)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.41  cnf(c_0_24, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k2_xboole_0(X1,esk4_0)))=k2_zfmisc_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.41  cnf(c_0_26, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  fof(c_0_27, plain, ![X19, X20, X21]:((~r1_tarski(k2_zfmisc_1(X20,X19),k2_zfmisc_1(X21,X19))|X19=k1_xboole_0|r1_tarski(X20,X21))&(~r1_tarski(k2_zfmisc_1(X19,X20),k2_zfmisc_1(X19,X21))|X19=k1_xboole_0|r1_tarski(X20,X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (k2_zfmisc_1(esk3_0,k2_xboole_0(esk4_0,esk4_0))=k2_zfmisc_1(esk1_0,k2_xboole_0(esk2_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_16])).
% 0.20/0.41  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_24])).
% 0.20/0.41  cnf(c_0_31, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,k2_xboole_0(X1,esk4_0)))=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.41  cnf(c_0_32, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (k2_zfmisc_1(esk1_0,k2_xboole_0(esk2_0,esk2_0))=k2_zfmisc_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_17]), c_0_30])])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_35, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.41  cnf(c_0_36, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0)=k2_zfmisc_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_31, c_0_20])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (r1_tarski(k2_xboole_0(esk2_0,esk2_0),X1)|~r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.20/0.41  fof(c_0_39, plain, ![X17, X18]:r1_tarski(X17,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (r1_tarski(X1,k3_xboole_0(esk1_0,esk3_0))|~r1_tarski(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.20/0.41  fof(c_0_41, plain, ![X13, X14]:r1_tarski(k3_xboole_0(X13,X14),X13), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.41  cnf(c_0_42, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (r1_tarski(k2_xboole_0(esk2_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_38, c_0_30])).
% 0.20/0.41  cnf(c_0_44, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (r1_tarski(esk1_0,k3_xboole_0(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_40, c_0_30])).
% 0.20/0.41  cnf(c_0_46, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (k2_xboole_0(esk2_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_45]), c_0_46])])).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,X1))), inference(rw,[status(thm)],[c_0_38, c_0_47])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,k2_xboole_0(X1,esk4_0)))=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_31, c_0_48])).
% 0.20/0.41  cnf(c_0_51, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (r1_tarski(esk2_0,k3_xboole_0(esk2_0,k2_xboole_0(X1,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_30])])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (k2_zfmisc_1(k2_xboole_0(esk1_0,esk3_0),esk2_0)=k2_zfmisc_1(esk3_0,k2_xboole_0(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_21, c_0_51])).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, (k3_xboole_0(esk2_0,k2_xboole_0(X1,esk4_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_52]), c_0_46])])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (r1_tarski(k2_xboole_0(esk1_0,esk3_0),X1)|~r1_tarski(k2_zfmisc_1(esk3_0,k2_xboole_0(esk2_0,esk4_0)),k2_zfmisc_1(X1,esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_53]), c_0_37])).
% 0.20/0.41  fof(c_0_56, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.41  cnf(c_0_57, negated_conjecture, (k3_xboole_0(esk2_0,k2_xboole_0(esk4_0,X1))=esk2_0), inference(spm,[status(thm)],[c_0_54, c_0_18])).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, (r1_tarski(k2_xboole_0(esk1_0,esk3_0),X1)|~r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(X1,esk2_0))|~r1_tarski(esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_29]), c_0_17])).
% 0.20/0.41  cnf(c_0_59, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (k3_xboole_0(esk2_0,X1)=esk2_0|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_57, c_0_29])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (r1_tarski(k2_xboole_0(esk1_0,esk3_0),esk1_0)|~r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_58, c_0_30])).
% 0.20/0.41  cnf(c_0_62, negated_conjecture, (k3_xboole_0(X1,esk2_0)=esk2_0|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.41  cnf(c_0_63, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_20, c_0_18])).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, (k2_xboole_0(esk1_0,esk3_0)=esk1_0|~r1_tarski(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_61]), c_0_44])])).
% 0.20/0.41  cnf(c_0_65, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_46, c_0_62])).
% 0.20/0.41  cnf(c_0_66, negated_conjecture, (esk3_0=esk1_0|~r1_tarski(esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_59]), c_0_48])).
% 0.20/0.41  cnf(c_0_67, negated_conjecture, (r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_65, c_0_30])).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, (esk3_0=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67])])).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, (esk1_0!=esk3_0|esk2_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_70, negated_conjecture, (k2_zfmisc_1(esk1_0,esk4_0)=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_17, c_0_68])).
% 0.20/0.41  cnf(c_0_71, negated_conjecture, (esk4_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_68])])).
% 0.20/0.41  cnf(c_0_72, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_70]), c_0_34])).
% 0.20/0.41  cnf(c_0_73, negated_conjecture, (~r1_tarski(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_67]), c_0_71])).
% 0.20/0.41  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_30]), c_0_73]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 75
% 0.20/0.41  # Proof object clause steps            : 52
% 0.20/0.41  # Proof object formula steps           : 23
% 0.20/0.41  # Proof object conjectures             : 40
% 0.20/0.41  # Proof object clause conjectures      : 37
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 17
% 0.20/0.41  # Proof object initial formulas used   : 11
% 0.20/0.41  # Proof object generating inferences   : 28
% 0.20/0.41  # Proof object simplifying inferences  : 33
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 11
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 18
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 18
% 0.20/0.41  # Processed clauses                    : 157
% 0.20/0.41  # ...of these trivial                  : 16
% 0.20/0.41  # ...subsumed                          : 28
% 0.20/0.41  # ...remaining for further processing  : 113
% 0.20/0.41  # Other redundant clauses eliminated   : 2
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 1
% 0.20/0.41  # Backward-rewritten                   : 41
% 0.20/0.41  # Generated clauses                    : 586
% 0.20/0.41  # ...of the previous two non-trivial   : 473
% 0.20/0.41  # Contextual simplify-reflections      : 0
% 0.20/0.41  # Paramodulations                      : 584
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 2
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 52
% 0.20/0.41  #    Positive orientable unit clauses  : 26
% 0.20/0.41  #    Positive unorientable unit clauses: 2
% 0.20/0.41  #    Negative unit clauses             : 4
% 0.20/0.41  #    Non-unit-clauses                  : 20
% 0.20/0.41  # Current number of unprocessed clauses: 325
% 0.20/0.41  # ...number of literals in the above   : 606
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 59
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 203
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 200
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 27
% 0.20/0.41  # Unit Clause-clause subsumption calls : 14
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 37
% 0.20/0.41  # BW rewrite match successes           : 26
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 8558
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.065 s
% 0.20/0.41  # System time              : 0.007 s
% 0.20/0.41  # Total time               : 0.072 s
% 0.20/0.41  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
