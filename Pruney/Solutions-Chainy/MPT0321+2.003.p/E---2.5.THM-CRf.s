%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:59 EST 2020

% Result     : Theorem 0.58s
% Output     : CNFRefutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 889 expanded)
%              Number of clauses        :   69 ( 407 expanded)
%              Number of leaves         :   14 ( 224 expanded)
%              Depth                    :   22
%              Number of atoms          :  171 (1846 expanded)
%              Number of equality atoms :  113 (1301 expanded)
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

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X30,X31] :
      ( ~ r1_tarski(X30,X31)
      | k3_xboole_0(X30,X31) = X30 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_16,plain,(
    ! [X36,X37] : r1_tarski(X36,k2_xboole_0(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_17,plain,(
    ! [X60,X61,X62] :
      ( k2_zfmisc_1(k2_xboole_0(X60,X61),X62) = k2_xboole_0(k2_zfmisc_1(X60,X62),k2_zfmisc_1(X61,X62))
      & k2_zfmisc_1(X62,k2_xboole_0(X60,X61)) = k2_xboole_0(k2_zfmisc_1(X62,X60),k2_zfmisc_1(X62,X61)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

fof(c_0_18,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k2_zfmisc_1(esk10_0,esk11_0)
    & esk8_0 != k1_xboole_0
    & esk9_0 != k1_xboole_0
    & ( esk8_0 != esk10_0
      | esk9_0 != esk11_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k2_zfmisc_1(esk10_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(X1,esk11_0)) = k2_zfmisc_1(k2_xboole_0(esk10_0,X1),esk11_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_25,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_26,plain,(
    ! [X63,X64,X65,X66] : k2_zfmisc_1(k3_xboole_0(X63,X64),k3_xboole_0(X65,X66)) = k3_xboole_0(k2_zfmisc_1(X63,X65),k2_zfmisc_1(X64,X66)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_27,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(k2_xboole_0(esk10_0,X1),esk11_0)) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_30,plain,(
    ! [X57,X58,X59] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X58,X57),k2_zfmisc_1(X59,X57))
        | X57 = k1_xboole_0
        | r1_tarski(X58,X59) )
      & ( ~ r1_tarski(k2_zfmisc_1(X57,X58),k2_zfmisc_1(X57,X59))
        | X57 = k1_xboole_0
        | r1_tarski(X58,X59) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_31,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(k2_xboole_0(X1,esk10_0),esk11_0)) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_xboole_0(X1,X3),X4)) = k2_zfmisc_1(X1,k3_xboole_0(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

fof(c_0_33,plain,(
    ! [X22,X23] :
      ( ( r1_tarski(X22,X23)
        | X22 != X23 )
      & ( r1_tarski(X23,X22)
        | X22 != X23 )
      & ( ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X22)
        | X22 = X23 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k3_xboole_0(esk9_0,esk11_0)) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk9_0,esk11_0),X1)
    | ~ r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk8_0,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_37])).

fof(c_0_40,plain,(
    ! [X24,X25] :
      ( ( k4_xboole_0(X24,X25) != k1_xboole_0
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | k4_xboole_0(X24,X25) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_41,plain,(
    ! [X26,X27] : k4_xboole_0(X26,X27) = k5_xboole_0(X26,k3_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk9_0,esk11_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(X1,k3_xboole_0(esk9_0,esk11_0))
    | ~ r1_tarski(k2_zfmisc_1(esk8_0,X1),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_48,plain,(
    ! [X13] : k3_xboole_0(X13,X13) = X13 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_49,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,X1)) = k2_zfmisc_1(esk10_0,k2_xboole_0(X1,esk11_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_22]),c_0_28])).

fof(c_0_50,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(X28,X29)
      | k2_xboole_0(X28,X29) = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( k3_xboole_0(esk9_0,esk11_0) = esk9_0
    | ~ r1_tarski(esk9_0,k3_xboole_0(esk9_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk9_0,k3_xboole_0(esk9_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_39])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( k2_zfmisc_1(k2_xboole_0(esk8_0,esk10_0),esk9_0) = k2_zfmisc_1(esk10_0,k2_xboole_0(esk9_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_49])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_51,c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(esk9_0,esk11_0) = esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_39]),c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(esk10_0,k2_xboole_0(esk9_0,esk11_0)),k2_zfmisc_1(X1,esk9_0)) = k2_zfmisc_1(k2_xboole_0(k2_xboole_0(esk8_0,esk10_0),X1),esk9_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_56])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_20])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk9_0,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])])).

cnf(c_0_64,negated_conjecture,
    ( k2_zfmisc_1(k2_xboole_0(esk10_0,k2_xboole_0(esk8_0,esk10_0)),esk9_0) = k2_zfmisc_1(esk10_0,k2_xboole_0(esk9_0,esk11_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_61]),c_0_28]),c_0_28]),c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( k2_xboole_0(esk9_0,esk11_0) = esk11_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_63])).

cnf(c_0_66,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_xboole_0(X1,X3),X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_67,negated_conjecture,
    ( k2_zfmisc_1(k2_xboole_0(esk10_0,k2_xboole_0(esk8_0,esk10_0)),esk9_0) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_22])).

fof(c_0_68,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_69,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,k2_xboole_0(X1,esk11_0))) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_49])).

cnf(c_0_70,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k2_xboole_0(X2,X4))) = k2_zfmisc_1(k3_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

fof(c_0_71,plain,(
    ! [X55,X56] :
      ( ( k2_zfmisc_1(X55,X56) != k1_xboole_0
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0 )
      & ( X55 != k1_xboole_0
        | k2_zfmisc_1(X55,X56) = k1_xboole_0 )
      & ( X56 != k1_xboole_0
        | k2_zfmisc_1(X55,X56) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_72,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(X1,esk11_0),k2_zfmisc_1(esk8_0,esk9_0)) = k2_zfmisc_1(k2_xboole_0(X1,esk10_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk10_0,esk9_0),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) = k2_zfmisc_1(k3_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_55])).

cnf(c_0_75,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),esk9_0) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( k2_zfmisc_1(k2_xboole_0(esk8_0,esk10_0),esk11_0) = k2_zfmisc_1(esk8_0,k2_xboole_0(esk9_0,esk11_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_72]),c_0_28])).

cnf(c_0_79,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r1_tarski(esk11_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_22])).

cnf(c_0_80,negated_conjecture,
    ( k2_zfmisc_1(esk10_0,esk9_0) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_73]),c_0_74]),c_0_75]),c_0_76])).

cnf(c_0_81,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_82,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k3_xboole_0(X3,X4) = k1_xboole_0
    | k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_29])).

cnf(c_0_83,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk8_0,k2_xboole_0(esk9_0,esk11_0))) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_85,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r1_tarski(esk11_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_39])])).

cnf(c_0_86,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_55]),c_0_23]),c_0_36]),c_0_84])).

cnf(c_0_88,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(esk11_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_85]),c_0_86]),c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(esk10_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(X1,esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_80]),c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( esk8_0 != esk10_0
    | esk9_0 != esk11_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_92,negated_conjecture,
    ( esk11_0 = esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_89]),c_0_63])])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(esk10_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_39])).

cnf(c_0_94,negated_conjecture,
    ( esk10_0 != esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92])])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(X1,esk10_0)
    | ~ r1_tarski(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_80]),c_0_84])).

cnf(c_0_96,negated_conjecture,
    ( ~ r1_tarski(esk8_0,esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_93]),c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_39]),c_0_96]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:21:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.58/0.75  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.58/0.75  # and selection function SelectNegativeLiterals.
% 0.58/0.75  #
% 0.58/0.75  # Preprocessing time       : 0.039 s
% 0.58/0.75  # Presaturation interreduction done
% 0.58/0.75  
% 0.58/0.75  # Proof found!
% 0.58/0.75  # SZS status Theorem
% 0.58/0.75  # SZS output start CNFRefutation
% 0.58/0.75  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.58/0.75  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.58/0.75  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.58/0.75  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 0.58/0.75  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.58/0.75  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.58/0.75  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 0.58/0.75  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.58/0.75  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.58/0.75  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.58/0.75  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.58/0.75  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.58/0.75  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.58/0.75  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.58/0.75  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 0.58/0.75  fof(c_0_15, plain, ![X30, X31]:(~r1_tarski(X30,X31)|k3_xboole_0(X30,X31)=X30), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.58/0.75  fof(c_0_16, plain, ![X36, X37]:r1_tarski(X36,k2_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.58/0.75  fof(c_0_17, plain, ![X60, X61, X62]:(k2_zfmisc_1(k2_xboole_0(X60,X61),X62)=k2_xboole_0(k2_zfmisc_1(X60,X62),k2_zfmisc_1(X61,X62))&k2_zfmisc_1(X62,k2_xboole_0(X60,X61))=k2_xboole_0(k2_zfmisc_1(X62,X60),k2_zfmisc_1(X62,X61))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 0.58/0.75  fof(c_0_18, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k2_zfmisc_1(esk10_0,esk11_0)&((esk8_0!=k1_xboole_0&esk9_0!=k1_xboole_0)&(esk8_0!=esk10_0|esk9_0!=esk11_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.58/0.75  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.58/0.75  cnf(c_0_20, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.58/0.75  cnf(c_0_21, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.58/0.75  cnf(c_0_22, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k2_zfmisc_1(esk10_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.58/0.75  cnf(c_0_23, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.58/0.75  cnf(c_0_24, negated_conjecture, (k2_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(X1,esk11_0))=k2_zfmisc_1(k2_xboole_0(esk10_0,X1),esk11_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.58/0.75  fof(c_0_25, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k2_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.58/0.75  fof(c_0_26, plain, ![X63, X64, X65, X66]:k2_zfmisc_1(k3_xboole_0(X63,X64),k3_xboole_0(X65,X66))=k3_xboole_0(k2_zfmisc_1(X63,X65),k2_zfmisc_1(X64,X66)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.58/0.75  cnf(c_0_27, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(k2_xboole_0(esk10_0,X1),esk11_0))=k2_zfmisc_1(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.58/0.75  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.58/0.75  cnf(c_0_29, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.58/0.75  fof(c_0_30, plain, ![X57, X58, X59]:((~r1_tarski(k2_zfmisc_1(X58,X57),k2_zfmisc_1(X59,X57))|X57=k1_xboole_0|r1_tarski(X58,X59))&(~r1_tarski(k2_zfmisc_1(X57,X58),k2_zfmisc_1(X57,X59))|X57=k1_xboole_0|r1_tarski(X58,X59))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 0.58/0.75  cnf(c_0_31, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(k2_xboole_0(X1,esk10_0),esk11_0))=k2_zfmisc_1(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.58/0.75  cnf(c_0_32, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_xboole_0(X1,X3),X4))=k2_zfmisc_1(X1,k3_xboole_0(X2,X4))), inference(spm,[status(thm)],[c_0_29, c_0_23])).
% 0.58/0.75  fof(c_0_33, plain, ![X22, X23]:(((r1_tarski(X22,X23)|X22!=X23)&(r1_tarski(X23,X22)|X22!=X23))&(~r1_tarski(X22,X23)|~r1_tarski(X23,X22)|X22=X23)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.58/0.75  cnf(c_0_34, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.58/0.75  cnf(c_0_35, negated_conjecture, (k2_zfmisc_1(esk8_0,k3_xboole_0(esk9_0,esk11_0))=k2_zfmisc_1(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.58/0.75  cnf(c_0_36, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.58/0.75  cnf(c_0_37, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.58/0.75  cnf(c_0_38, negated_conjecture, (r1_tarski(k3_xboole_0(esk9_0,esk11_0),X1)|~r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk8_0,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.58/0.75  cnf(c_0_39, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_37])).
% 0.58/0.75  fof(c_0_40, plain, ![X24, X25]:((k4_xboole_0(X24,X25)!=k1_xboole_0|r1_tarski(X24,X25))&(~r1_tarski(X24,X25)|k4_xboole_0(X24,X25)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.58/0.75  fof(c_0_41, plain, ![X26, X27]:k4_xboole_0(X26,X27)=k5_xboole_0(X26,k3_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.58/0.75  cnf(c_0_42, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.58/0.75  cnf(c_0_43, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.58/0.75  cnf(c_0_44, negated_conjecture, (r1_tarski(k3_xboole_0(esk9_0,esk11_0),esk9_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.58/0.75  cnf(c_0_45, negated_conjecture, (r1_tarski(X1,k3_xboole_0(esk9_0,esk11_0))|~r1_tarski(k2_zfmisc_1(esk8_0,X1),k2_zfmisc_1(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.58/0.75  cnf(c_0_46, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.58/0.75  cnf(c_0_47, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.58/0.75  fof(c_0_48, plain, ![X13]:k3_xboole_0(X13,X13)=X13, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.58/0.75  cnf(c_0_49, negated_conjecture, (k2_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,X1))=k2_zfmisc_1(esk10_0,k2_xboole_0(X1,esk11_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_22]), c_0_28])).
% 0.58/0.75  fof(c_0_50, plain, ![X28, X29]:(~r1_tarski(X28,X29)|k2_xboole_0(X28,X29)=X29), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.58/0.75  cnf(c_0_51, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.58/0.75  cnf(c_0_52, negated_conjecture, (k3_xboole_0(esk9_0,esk11_0)=esk9_0|~r1_tarski(esk9_0,k3_xboole_0(esk9_0,esk11_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.58/0.75  cnf(c_0_53, negated_conjecture, (r1_tarski(esk9_0,k3_xboole_0(esk9_0,esk11_0))), inference(spm,[status(thm)],[c_0_45, c_0_39])).
% 0.58/0.75  cnf(c_0_54, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.58/0.75  cnf(c_0_55, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.58/0.75  cnf(c_0_56, negated_conjecture, (k2_zfmisc_1(k2_xboole_0(esk8_0,esk10_0),esk9_0)=k2_zfmisc_1(esk10_0,k2_xboole_0(esk9_0,esk11_0))), inference(spm,[status(thm)],[c_0_21, c_0_49])).
% 0.58/0.75  cnf(c_0_57, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.58/0.75  cnf(c_0_58, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_51, c_0_47])).
% 0.58/0.75  cnf(c_0_59, negated_conjecture, (k3_xboole_0(esk9_0,esk11_0)=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53])])).
% 0.58/0.75  cnf(c_0_60, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_39]), c_0_55])).
% 0.58/0.75  cnf(c_0_61, negated_conjecture, (k2_xboole_0(k2_zfmisc_1(esk10_0,k2_xboole_0(esk9_0,esk11_0)),k2_zfmisc_1(X1,esk9_0))=k2_zfmisc_1(k2_xboole_0(k2_xboole_0(esk8_0,esk10_0),X1),esk9_0)), inference(spm,[status(thm)],[c_0_21, c_0_56])).
% 0.58/0.75  cnf(c_0_62, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_57, c_0_20])).
% 0.58/0.75  cnf(c_0_63, negated_conjecture, (r1_tarski(esk9_0,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])])).
% 0.58/0.75  cnf(c_0_64, negated_conjecture, (k2_zfmisc_1(k2_xboole_0(esk10_0,k2_xboole_0(esk8_0,esk10_0)),esk9_0)=k2_zfmisc_1(esk10_0,k2_xboole_0(esk9_0,esk11_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_61]), c_0_28]), c_0_28]), c_0_62])).
% 0.58/0.75  cnf(c_0_65, negated_conjecture, (k2_xboole_0(esk9_0,esk11_0)=esk11_0), inference(spm,[status(thm)],[c_0_57, c_0_63])).
% 0.58/0.75  cnf(c_0_66, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_xboole_0(X1,X3),X2))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.58/0.75  cnf(c_0_67, negated_conjecture, (k2_zfmisc_1(k2_xboole_0(esk10_0,k2_xboole_0(esk8_0,esk10_0)),esk9_0)=k2_zfmisc_1(esk8_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_22])).
% 0.58/0.75  fof(c_0_68, plain, ![X9, X10]:k3_xboole_0(X9,X10)=k3_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.58/0.75  cnf(c_0_69, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,k2_xboole_0(X1,esk11_0)))=k2_zfmisc_1(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_23, c_0_49])).
% 0.58/0.75  cnf(c_0_70, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k2_xboole_0(X2,X4)))=k2_zfmisc_1(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_29, c_0_23])).
% 0.58/0.75  fof(c_0_71, plain, ![X55, X56]:((k2_zfmisc_1(X55,X56)!=k1_xboole_0|(X55=k1_xboole_0|X56=k1_xboole_0))&((X55!=k1_xboole_0|k2_zfmisc_1(X55,X56)=k1_xboole_0)&(X56!=k1_xboole_0|k2_zfmisc_1(X55,X56)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.58/0.75  cnf(c_0_72, negated_conjecture, (k2_xboole_0(k2_zfmisc_1(X1,esk11_0),k2_zfmisc_1(esk8_0,esk9_0))=k2_zfmisc_1(k2_xboole_0(X1,esk10_0),esk11_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.58/0.75  cnf(c_0_73, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk10_0,esk9_0),k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.58/0.75  cnf(c_0_74, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))=k2_zfmisc_1(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_29, c_0_55])).
% 0.58/0.75  cnf(c_0_75, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.58/0.75  cnf(c_0_76, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),esk9_0)=k2_zfmisc_1(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.58/0.75  cnf(c_0_77, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.58/0.75  cnf(c_0_78, negated_conjecture, (k2_zfmisc_1(k2_xboole_0(esk8_0,esk10_0),esk11_0)=k2_zfmisc_1(esk8_0,k2_xboole_0(esk9_0,esk11_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_72]), c_0_28])).
% 0.58/0.75  cnf(c_0_79, negated_conjecture, (esk10_0=k1_xboole_0|r1_tarski(esk11_0,X1)|~r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,X1))), inference(spm,[status(thm)],[c_0_34, c_0_22])).
% 0.58/0.75  cnf(c_0_80, negated_conjecture, (k2_zfmisc_1(esk10_0,esk9_0)=k2_zfmisc_1(esk8_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_73]), c_0_74]), c_0_75]), c_0_76])).
% 0.58/0.75  cnf(c_0_81, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.58/0.75  cnf(c_0_82, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|k3_xboole_0(X3,X4)=k1_xboole_0|k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_29])).
% 0.58/0.75  cnf(c_0_83, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk8_0,k2_xboole_0(esk9_0,esk11_0)))=k2_zfmisc_1(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_31, c_0_78])).
% 0.58/0.75  cnf(c_0_84, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.58/0.75  cnf(c_0_85, negated_conjecture, (esk10_0=k1_xboole_0|r1_tarski(esk11_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_39])])).
% 0.58/0.75  cnf(c_0_86, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_81])).
% 0.58/0.75  cnf(c_0_87, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_55]), c_0_23]), c_0_36]), c_0_84])).
% 0.58/0.75  cnf(c_0_88, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.58/0.75  cnf(c_0_89, negated_conjecture, (r1_tarski(esk11_0,esk9_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_85]), c_0_86]), c_0_87])).
% 0.58/0.75  cnf(c_0_90, negated_conjecture, (r1_tarski(esk10_0,X1)|~r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(X1,esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_80]), c_0_84])).
% 0.58/0.75  cnf(c_0_91, negated_conjecture, (esk8_0!=esk10_0|esk9_0!=esk11_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.58/0.75  cnf(c_0_92, negated_conjecture, (esk11_0=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_89]), c_0_63])])).
% 0.58/0.75  cnf(c_0_93, negated_conjecture, (r1_tarski(esk10_0,esk8_0)), inference(spm,[status(thm)],[c_0_90, c_0_39])).
% 0.58/0.75  cnf(c_0_94, negated_conjecture, (esk10_0!=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_92])])).
% 0.58/0.75  cnf(c_0_95, negated_conjecture, (r1_tarski(X1,esk10_0)|~r1_tarski(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_80]), c_0_84])).
% 0.58/0.75  cnf(c_0_96, negated_conjecture, (~r1_tarski(esk8_0,esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_93]), c_0_94])).
% 0.58/0.75  cnf(c_0_97, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_39]), c_0_96]), ['proof']).
% 0.58/0.75  # SZS output end CNFRefutation
% 0.58/0.75  # Proof object total steps             : 98
% 0.58/0.75  # Proof object clause steps            : 69
% 0.58/0.75  # Proof object formula steps           : 29
% 0.58/0.75  # Proof object conjectures             : 42
% 0.58/0.75  # Proof object clause conjectures      : 39
% 0.58/0.75  # Proof object formula conjectures     : 3
% 0.58/0.75  # Proof object initial clauses used    : 22
% 0.58/0.75  # Proof object initial formulas used   : 14
% 0.58/0.75  # Proof object generating inferences   : 40
% 0.58/0.75  # Proof object simplifying inferences  : 37
% 0.58/0.75  # Training examples: 0 positive, 0 negative
% 0.58/0.75  # Parsed axioms                        : 21
% 0.58/0.75  # Removed by relevancy pruning/SinE    : 0
% 0.58/0.75  # Initial clauses                      : 40
% 0.58/0.75  # Removed in clause preprocessing      : 1
% 0.58/0.75  # Initial clauses in saturation        : 39
% 0.58/0.75  # Processed clauses                    : 2144
% 0.58/0.75  # ...of these trivial                  : 660
% 0.58/0.75  # ...subsumed                          : 851
% 0.58/0.75  # ...remaining for further processing  : 633
% 0.58/0.75  # Other redundant clauses eliminated   : 322
% 0.58/0.75  # Clauses deleted for lack of memory   : 0
% 0.58/0.75  # Backward-subsumed                    : 27
% 0.58/0.75  # Backward-rewritten                   : 255
% 0.58/0.75  # Generated clauses                    : 53706
% 0.58/0.75  # ...of the previous two non-trivial   : 35089
% 0.58/0.75  # Contextual simplify-reflections      : 5
% 0.58/0.75  # Paramodulations                      : 53377
% 0.58/0.75  # Factorizations                       : 8
% 0.58/0.75  # Equation resolutions                 : 322
% 0.58/0.75  # Propositional unsat checks           : 0
% 0.58/0.75  #    Propositional check models        : 0
% 0.58/0.75  #    Propositional check unsatisfiable : 0
% 0.58/0.75  #    Propositional clauses             : 0
% 0.58/0.75  #    Propositional clauses after purity: 0
% 0.58/0.75  #    Propositional unsat core size     : 0
% 0.58/0.75  #    Propositional preprocessing time  : 0.000
% 0.58/0.75  #    Propositional encoding time       : 0.000
% 0.58/0.75  #    Propositional solver time         : 0.000
% 0.58/0.75  #    Success case prop preproc time    : 0.000
% 0.58/0.75  #    Success case prop encoding time   : 0.000
% 0.58/0.75  #    Success case prop solver time     : 0.000
% 0.58/0.75  # Current number of processed clauses  : 305
% 0.58/0.75  #    Positive orientable unit clauses  : 105
% 0.58/0.75  #    Positive unorientable unit clauses: 4
% 0.58/0.75  #    Negative unit clauses             : 8
% 0.58/0.75  #    Non-unit-clauses                  : 188
% 0.58/0.75  # Current number of unprocessed clauses: 32052
% 0.58/0.75  # ...number of literals in the above   : 72832
% 0.58/0.75  # Current number of archived formulas  : 0
% 0.58/0.75  # Current number of archived clauses   : 321
% 0.58/0.75  # Clause-clause subsumption calls (NU) : 11155
% 0.58/0.75  # Rec. Clause-clause subsumption calls : 9875
% 0.58/0.75  # Non-unit clause-clause subsumptions  : 699
% 0.58/0.75  # Unit Clause-clause subsumption calls : 1198
% 0.58/0.75  # Rewrite failures with RHS unbound    : 0
% 0.58/0.75  # BW rewrite match attempts            : 177
% 0.58/0.75  # BW rewrite match successes           : 123
% 0.58/0.75  # Condensation attempts                : 0
% 0.58/0.75  # Condensation successes               : 0
% 0.58/0.75  # Termbank termtop insertions          : 719714
% 0.58/0.75  
% 0.58/0.75  # -------------------------------------------------
% 0.58/0.75  # User time                : 0.387 s
% 0.58/0.75  # System time              : 0.022 s
% 0.58/0.75  # Total time               : 0.409 s
% 0.58/0.75  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
