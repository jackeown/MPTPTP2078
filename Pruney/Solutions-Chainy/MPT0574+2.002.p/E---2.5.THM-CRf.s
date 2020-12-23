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
% DateTime   : Thu Dec  3 10:51:48 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 390 expanded)
%              Number of clauses        :   61 ( 184 expanded)
%              Number of leaves         :   20 ( 100 expanded)
%              Depth                    :   13
%              Number of atoms          :  198 ( 593 expanded)
%              Number of equality atoms :   80 ( 343 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t178_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_20,plain,(
    ! [X55,X56] : k1_setfam_1(k2_tarski(X55,X56)) = k3_xboole_0(X55,X56) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_21,plain,(
    ! [X51,X52] : k1_enumset1(X51,X51,X52) = k2_tarski(X51,X52) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X26,X27] : k4_xboole_0(X26,X27) = k5_xboole_0(X26,k3_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_23,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( r2_hidden(X17,X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X20)
        | X21 = k4_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X20)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_28,plain,(
    ! [X34,X35] :
      ( ~ r1_tarski(X34,X35)
      | k3_xboole_0(X34,X35) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t178_relat_1])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_32,plain,(
    ! [X23] : k3_xboole_0(X23,X23) = X23 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_33,plain,(
    ! [X40] : k4_xboole_0(X40,k1_xboole_0) = X40 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_34,plain,(
    ! [X36,X37] : r1_tarski(k4_xboole_0(X36,X37),X36) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

fof(c_0_37,plain,(
    ! [X28,X29] : r1_tarski(k3_xboole_0(X28,X29),X28) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_38,plain,
    ( X3 != k5_xboole_0(X4,k1_setfam_1(k1_enumset1(X4,X4,X2)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_41,plain,(
    ! [X31,X32,X33] :
      ( ~ r1_tarski(X31,X32)
      | ~ r1_tarski(X32,X33)
      | r1_tarski(X31,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_42,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_45,plain,(
    ! [X53,X54] : k3_tarski(k2_tarski(X53,X54)) = k2_xboole_0(X53,X54) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_46,plain,(
    ! [X41] :
      ( ~ r1_tarski(X41,k1_xboole_0)
      | X41 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_47,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_48,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3))))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_39,c_0_27])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_40,c_0_31])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_42,c_0_31])).

cnf(c_0_54,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(esk3_0,esk3_0,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_55,plain,(
    ! [X49,X50] : k2_tarski(X49,X50) = k2_tarski(X50,X49) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_57,plain,(
    ! [X42,X43] : r1_tarski(X42,k2_xboole_0(X42,X43)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_58,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_59,plain,(
    ! [X57,X58,X59] :
      ( ~ v1_relat_1(X59)
      | k10_relat_1(X59,k2_xboole_0(X57,X58)) = k2_xboole_0(k10_relat_1(X59,X57),k10_relat_1(X59,X58)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_47,c_0_27])).

cnf(c_0_62,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_50])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_44])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_67,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X4)))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_56,c_0_31])).

fof(c_0_69,plain,(
    ! [X30] : k2_xboole_0(X30,k1_xboole_0) = X30 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_71,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_58,c_0_24])).

cnf(c_0_72,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_73,plain,(
    ! [X38,X39] : k2_xboole_0(X38,k4_xboole_0(X39,X38)) = k2_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_74,plain,
    ( k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_75,plain,
    ( X3 = k1_setfam_1(k1_enumset1(X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_62,c_0_27])).

cnf(c_0_76,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_78,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_24]),c_0_24])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3)))) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_80,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_82,plain,
    ( k10_relat_1(X1,k3_tarski(k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_71]),c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_84,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_85,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X2) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_74]),c_0_74]),c_0_74]),c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(esk4_0,esk4_0,k5_xboole_0(esk3_0,esk3_0))) = k5_xboole_0(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_77]),c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( ~ r2_hidden(X1,k5_xboole_0(esk3_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_54]),c_0_63])).

cnf(c_0_88,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_80,c_0_71])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( k3_tarski(k1_enumset1(k10_relat_1(esk5_0,X1),k10_relat_1(esk5_0,X1),k10_relat_1(esk5_0,X2))) = k10_relat_1(esk5_0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_91,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X1))))) = k3_tarski(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_71]),c_0_71]),c_0_31])).

cnf(c_0_92,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

cnf(c_0_93,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_88,c_0_78])).

fof(c_0_94,plain,(
    ! [X24,X25] :
      ( ( r1_tarski(X24,X25)
        | X24 != X25 )
      & ( r1_tarski(X25,X24)
        | X24 != X25 )
      & ( ~ r1_tarski(X24,X25)
        | ~ r1_tarski(X25,X24)
        | X24 = X25 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk5_0,X1),X2)
    | ~ r1_tarski(k10_relat_1(esk5_0,k3_tarski(k1_enumset1(X1,X1,X3))),X2) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_54]),c_0_78]),c_0_92]),c_0_78]),c_0_93])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk5_0,esk3_0),X1)
    | ~ r1_tarski(k10_relat_1(esk5_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_99,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:19:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.78/0.93  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.78/0.93  # and selection function SelectNegativeLiterals.
% 0.78/0.93  #
% 0.78/0.93  # Preprocessing time       : 0.028 s
% 0.78/0.93  # Presaturation interreduction done
% 0.78/0.93  
% 0.78/0.93  # Proof found!
% 0.78/0.93  # SZS status Theorem
% 0.78/0.93  # SZS output start CNFRefutation
% 0.78/0.93  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.78/0.93  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.78/0.93  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.78/0.93  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.78/0.93  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.78/0.93  fof(t178_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 0.78/0.93  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.78/0.93  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.78/0.93  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.78/0.93  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.78/0.93  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.78/0.93  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.78/0.93  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.78/0.93  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.78/0.93  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.78/0.93  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.78/0.93  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 0.78/0.93  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.78/0.93  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.78/0.93  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.78/0.93  fof(c_0_20, plain, ![X55, X56]:k1_setfam_1(k2_tarski(X55,X56))=k3_xboole_0(X55,X56), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.78/0.93  fof(c_0_21, plain, ![X51, X52]:k1_enumset1(X51,X51,X52)=k2_tarski(X51,X52), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.78/0.93  fof(c_0_22, plain, ![X26, X27]:k4_xboole_0(X26,X27)=k5_xboole_0(X26,k3_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.78/0.93  cnf(c_0_23, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.78/0.93  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.78/0.93  fof(c_0_25, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:((((r2_hidden(X17,X14)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15))&(~r2_hidden(X17,X15)|~r2_hidden(X17,X16)|X16!=k4_xboole_0(X14,X15)))&(~r2_hidden(X18,X14)|r2_hidden(X18,X15)|r2_hidden(X18,X16)|X16!=k4_xboole_0(X14,X15)))&((~r2_hidden(esk2_3(X19,X20,X21),X21)|(~r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X20))|X21=k4_xboole_0(X19,X20))&((r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))&(~r2_hidden(esk2_3(X19,X20,X21),X20)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k4_xboole_0(X19,X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.78/0.93  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.78/0.93  cnf(c_0_27, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.78/0.93  fof(c_0_28, plain, ![X34, X35]:(~r1_tarski(X34,X35)|k3_xboole_0(X34,X35)=X34), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.78/0.93  fof(c_0_29, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t178_relat_1])).
% 0.78/0.93  cnf(c_0_30, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.78/0.93  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.78/0.93  fof(c_0_32, plain, ![X23]:k3_xboole_0(X23,X23)=X23, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.78/0.93  fof(c_0_33, plain, ![X40]:k4_xboole_0(X40,k1_xboole_0)=X40, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.78/0.93  fof(c_0_34, plain, ![X36, X37]:r1_tarski(k4_xboole_0(X36,X37),X36), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.78/0.93  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.78/0.93  fof(c_0_36, negated_conjecture, (v1_relat_1(esk5_0)&(r1_tarski(esk3_0,esk4_0)&~r1_tarski(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.78/0.93  fof(c_0_37, plain, ![X28, X29]:r1_tarski(k3_xboole_0(X28,X29),X28), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.78/0.93  cnf(c_0_38, plain, (X3!=k5_xboole_0(X4,k1_setfam_1(k1_enumset1(X4,X4,X2)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.78/0.93  cnf(c_0_39, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.78/0.93  cnf(c_0_40, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.78/0.93  fof(c_0_41, plain, ![X31, X32, X33]:(~r1_tarski(X31,X32)|~r1_tarski(X32,X33)|r1_tarski(X31,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.78/0.93  cnf(c_0_42, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.78/0.93  cnf(c_0_43, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_27])).
% 0.78/0.93  cnf(c_0_44, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.78/0.93  fof(c_0_45, plain, ![X53, X54]:k3_tarski(k2_tarski(X53,X54))=k2_xboole_0(X53,X54), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.78/0.93  fof(c_0_46, plain, ![X41]:(~r1_tarski(X41,k1_xboole_0)|X41=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.78/0.93  cnf(c_0_47, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.78/0.93  fof(c_0_48, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.78/0.93  cnf(c_0_49, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3))))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_38])).
% 0.78/0.93  cnf(c_0_50, plain, (k1_setfam_1(k1_enumset1(X1,X1,X1))=X1), inference(rw,[status(thm)],[c_0_39, c_0_27])).
% 0.78/0.93  cnf(c_0_51, plain, (k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_40, c_0_31])).
% 0.78/0.93  cnf(c_0_52, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.78/0.93  cnf(c_0_53, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X1)), inference(rw,[status(thm)],[c_0_42, c_0_31])).
% 0.78/0.93  cnf(c_0_54, negated_conjecture, (k1_setfam_1(k1_enumset1(esk3_0,esk3_0,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.78/0.93  fof(c_0_55, plain, ![X49, X50]:k2_tarski(X49,X50)=k2_tarski(X50,X49), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.78/0.93  cnf(c_0_56, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.78/0.93  fof(c_0_57, plain, ![X42, X43]:r1_tarski(X42,k2_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.78/0.93  cnf(c_0_58, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.78/0.93  fof(c_0_59, plain, ![X57, X58, X59]:(~v1_relat_1(X59)|k10_relat_1(X59,k2_xboole_0(X57,X58))=k2_xboole_0(k10_relat_1(X59,X57),k10_relat_1(X59,X58))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 0.78/0.93  cnf(c_0_60, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.78/0.93  cnf(c_0_61, plain, (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X1)), inference(rw,[status(thm)],[c_0_47, c_0_27])).
% 0.78/0.93  cnf(c_0_62, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.78/0.93  cnf(c_0_63, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.78/0.93  cnf(c_0_64, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_50])).
% 0.78/0.93  cnf(c_0_65, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_52, c_0_44])).
% 0.78/0.93  cnf(c_0_66, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.78/0.93  cnf(c_0_67, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.78/0.93  cnf(c_0_68, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X4)))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_56, c_0_31])).
% 0.78/0.93  fof(c_0_69, plain, ![X30]:k2_xboole_0(X30,k1_xboole_0)=X30, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.78/0.93  cnf(c_0_70, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.78/0.93  cnf(c_0_71, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_58, c_0_24])).
% 0.78/0.93  cnf(c_0_72, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.78/0.93  fof(c_0_73, plain, ![X38, X39]:k2_xboole_0(X38,k4_xboole_0(X39,X38))=k2_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.78/0.93  cnf(c_0_74, plain, (k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.78/0.93  cnf(c_0_75, plain, (X3=k1_setfam_1(k1_enumset1(X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_62, c_0_27])).
% 0.78/0.93  cnf(c_0_76, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.78/0.93  cnf(c_0_77, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.78/0.93  cnf(c_0_78, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_24]), c_0_24])).
% 0.78/0.93  cnf(c_0_79, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3))))), inference(er,[status(thm)],[c_0_68])).
% 0.78/0.93  cnf(c_0_80, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.78/0.93  cnf(c_0_81, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 0.78/0.93  cnf(c_0_82, plain, (k10_relat_1(X1,k3_tarski(k1_enumset1(X2,X2,X3)))=k3_tarski(k1_enumset1(k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_71]), c_0_71])).
% 0.78/0.93  cnf(c_0_83, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.78/0.93  cnf(c_0_84, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.78/0.93  cnf(c_0_85, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X2)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_74]), c_0_74]), c_0_74]), c_0_76])).
% 0.78/0.93  cnf(c_0_86, negated_conjecture, (k1_setfam_1(k1_enumset1(esk4_0,esk4_0,k5_xboole_0(esk3_0,esk3_0)))=k5_xboole_0(esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_77]), c_0_78])).
% 0.78/0.93  cnf(c_0_87, negated_conjecture, (~r2_hidden(X1,k5_xboole_0(esk3_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_54]), c_0_63])).
% 0.78/0.93  cnf(c_0_88, plain, (k3_tarski(k1_enumset1(X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_80, c_0_71])).
% 0.78/0.93  cnf(c_0_89, plain, (r1_tarski(X1,X2)|~r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)), inference(spm,[status(thm)],[c_0_52, c_0_81])).
% 0.78/0.93  cnf(c_0_90, negated_conjecture, (k3_tarski(k1_enumset1(k10_relat_1(esk5_0,X1),k10_relat_1(esk5_0,X1),k10_relat_1(esk5_0,X2)))=k10_relat_1(esk5_0,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.78/0.93  cnf(c_0_91, plain, (k3_tarski(k1_enumset1(X1,X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X1)))))=k3_tarski(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_71]), c_0_71]), c_0_31])).
% 0.78/0.93  cnf(c_0_92, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87])).
% 0.78/0.93  cnf(c_0_93, plain, (k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_88, c_0_78])).
% 0.78/0.93  fof(c_0_94, plain, ![X24, X25]:(((r1_tarski(X24,X25)|X24!=X25)&(r1_tarski(X25,X24)|X24!=X25))&(~r1_tarski(X24,X25)|~r1_tarski(X25,X24)|X24=X25)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.78/0.93  cnf(c_0_95, negated_conjecture, (r1_tarski(k10_relat_1(esk5_0,X1),X2)|~r1_tarski(k10_relat_1(esk5_0,k3_tarski(k1_enumset1(X1,X1,X3))),X2)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.78/0.93  cnf(c_0_96, negated_conjecture, (k3_tarski(k1_enumset1(esk3_0,esk3_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_54]), c_0_78]), c_0_92]), c_0_78]), c_0_93])).
% 0.78/0.93  cnf(c_0_97, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.78/0.93  cnf(c_0_98, negated_conjecture, (r1_tarski(k10_relat_1(esk5_0,esk3_0),X1)|~r1_tarski(k10_relat_1(esk5_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.78/0.93  cnf(c_0_99, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_97])).
% 0.78/0.93  cnf(c_0_100, negated_conjecture, (~r1_tarski(k10_relat_1(esk5_0,esk3_0),k10_relat_1(esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.78/0.93  cnf(c_0_101, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100]), ['proof']).
% 0.78/0.93  # SZS output end CNFRefutation
% 0.78/0.93  # Proof object total steps             : 102
% 0.78/0.93  # Proof object clause steps            : 61
% 0.78/0.93  # Proof object formula steps           : 41
% 0.78/0.93  # Proof object conjectures             : 18
% 0.78/0.93  # Proof object clause conjectures      : 15
% 0.78/0.93  # Proof object formula conjectures     : 3
% 0.78/0.93  # Proof object initial clauses used    : 23
% 0.78/0.93  # Proof object initial formulas used   : 20
% 0.78/0.93  # Proof object generating inferences   : 19
% 0.78/0.93  # Proof object simplifying inferences  : 35
% 0.78/0.93  # Training examples: 0 positive, 0 negative
% 0.78/0.93  # Parsed axioms                        : 22
% 0.78/0.93  # Removed by relevancy pruning/SinE    : 0
% 0.78/0.93  # Initial clauses                      : 37
% 0.78/0.93  # Removed in clause preprocessing      : 4
% 0.78/0.93  # Initial clauses in saturation        : 33
% 0.78/0.93  # Processed clauses                    : 2445
% 0.78/0.93  # ...of these trivial                  : 160
% 0.78/0.93  # ...subsumed                          : 1667
% 0.78/0.93  # ...remaining for further processing  : 618
% 0.78/0.93  # Other redundant clauses eliminated   : 525
% 0.78/0.93  # Clauses deleted for lack of memory   : 0
% 0.78/0.93  # Backward-subsumed                    : 14
% 0.78/0.93  # Backward-rewritten                   : 65
% 0.78/0.93  # Generated clauses                    : 58774
% 0.78/0.93  # ...of the previous two non-trivial   : 49772
% 0.78/0.93  # Contextual simplify-reflections      : 8
% 0.78/0.93  # Paramodulations                      : 58249
% 0.78/0.93  # Factorizations                       : 0
% 0.78/0.93  # Equation resolutions                 : 525
% 0.78/0.93  # Propositional unsat checks           : 0
% 0.78/0.93  #    Propositional check models        : 0
% 0.78/0.93  #    Propositional check unsatisfiable : 0
% 0.78/0.93  #    Propositional clauses             : 0
% 0.78/0.93  #    Propositional clauses after purity: 0
% 0.78/0.93  #    Propositional unsat core size     : 0
% 0.78/0.93  #    Propositional preprocessing time  : 0.000
% 0.78/0.93  #    Propositional encoding time       : 0.000
% 0.78/0.93  #    Propositional solver time         : 0.000
% 0.78/0.93  #    Success case prop preproc time    : 0.000
% 0.78/0.93  #    Success case prop encoding time   : 0.000
% 0.78/0.93  #    Success case prop solver time     : 0.000
% 0.78/0.93  # Current number of processed clauses  : 498
% 0.78/0.93  #    Positive orientable unit clauses  : 92
% 0.78/0.93  #    Positive unorientable unit clauses: 1
% 0.78/0.93  #    Negative unit clauses             : 7
% 0.78/0.93  #    Non-unit-clauses                  : 398
% 0.78/0.93  # Current number of unprocessed clauses: 46946
% 0.78/0.93  # ...number of literals in the above   : 215615
% 0.78/0.93  # Current number of archived formulas  : 0
% 0.78/0.93  # Current number of archived clauses   : 115
% 0.78/0.93  # Clause-clause subsumption calls (NU) : 57632
% 0.78/0.93  # Rec. Clause-clause subsumption calls : 36390
% 0.78/0.93  # Non-unit clause-clause subsumptions  : 1255
% 0.78/0.93  # Unit Clause-clause subsumption calls : 1104
% 0.78/0.93  # Rewrite failures with RHS unbound    : 0
% 0.78/0.93  # BW rewrite match attempts            : 288
% 0.78/0.93  # BW rewrite match successes           : 55
% 0.78/0.93  # Condensation attempts                : 0
% 0.78/0.93  # Condensation successes               : 0
% 0.78/0.93  # Termbank termtop insertions          : 1160564
% 0.78/0.93  
% 0.78/0.93  # -------------------------------------------------
% 0.78/0.93  # User time                : 0.560 s
% 0.78/0.93  # System time              : 0.024 s
% 0.78/0.93  # Total time               : 0.584 s
% 0.78/0.93  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
