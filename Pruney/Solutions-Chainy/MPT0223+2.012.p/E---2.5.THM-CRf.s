%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:48 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  124 (48922 expanded)
%              Number of clauses        :   83 (21511 expanded)
%              Number of leaves         :   20 (13700 expanded)
%              Depth                    :   20
%              Number of atoms          :  175 (49034 expanded)
%              Number of equality atoms :  157 (49007 expanded)
%              Maximal formula depth    :   22 (   2 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(t18_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_20,plain,(
    ! [X23,X24] : k3_xboole_0(X23,X24) = k5_xboole_0(k5_xboole_0(X23,X24),k2_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_21,plain,(
    ! [X21,X22] : k2_xboole_0(X21,X22) = k5_xboole_0(k5_xboole_0(X21,X22),k3_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_22,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_23,plain,(
    ! [X19,X20] : k2_xboole_0(X19,X20) = k2_xboole_0(k5_xboole_0(X19,X20),k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X17] : k3_xboole_0(X17,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_29,plain,(
    ! [X18] : k5_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_25]),c_0_25])).

cnf(c_0_32,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_25]),c_0_25])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X15,X16] : k3_xboole_0(X15,k2_xboole_0(X15,X16)) = X15 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1))) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_33]),c_0_34]),c_0_34]),c_0_34])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_39,c_0_25])).

fof(c_0_42,plain,(
    ! [X10] : k2_xboole_0(X10,X10) = X10 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_43,plain,
    ( k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_45,plain,(
    ! [X11] : k3_xboole_0(X11,X11) = X11 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_46,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_40]),c_0_34]),c_0_30])).

cnf(c_0_47,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_44,c_0_25])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_41,c_0_31])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_46]),c_0_34])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),X1) = X1 ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_52,plain,(
    ! [X12,X13,X14] : k5_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(X14,X13)) = k3_xboole_0(k5_xboole_0(X12,X14),X13) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[c_0_51,c_0_38])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_50])).

cnf(c_0_57,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_46]),c_0_54])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))),X2) = k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_41])).

cnf(c_0_59,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_56]),c_0_56]),c_0_50])).

cnf(c_0_60,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_50]),c_0_50])).

cnf(c_0_61,plain,
    ( k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),X3),k3_xboole_0(X1,X2)) = k3_xboole_0(X3,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_40]),c_0_54])).

cnf(c_0_62,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X2,X1))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_50])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_41,c_0_50])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),X2) = k3_xboole_0(k5_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_48])).

cnf(c_0_65,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),X3),k5_xboole_0(X1,X2)) = k3_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_46]),c_0_54])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))),X2) = k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_50]),c_0_50])).

cnf(c_0_67,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X2,X1))) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_48])).

cnf(c_0_69,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X2,X1))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_60]),c_0_46]),c_0_54])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1)),X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_64]),c_0_55])).

fof(c_0_71,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t18_zfmisc_1])).

cnf(c_0_72,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),k5_xboole_0(X2,X1)) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_60]),c_0_48])).

cnf(c_0_73,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X2,X1))) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_53])).

cnf(c_0_74,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),k3_xboole_0(X2,X1)) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_67]),c_0_68]),c_0_69]),c_0_59])).

cnf(c_0_75,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X2,X1)),X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_70,c_0_50])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_48])).

cnf(c_0_77,plain,
    ( k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X2,X1))),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_53])).

cnf(c_0_78,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_38]),c_0_38])).

fof(c_0_79,plain,(
    ! [X36,X37,X38,X39] : k2_enumset1(X36,X37,X38,X39) = k2_xboole_0(k1_enumset1(X36,X37,X38),k1_tarski(X39)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

fof(c_0_80,plain,(
    ! [X40] : k2_tarski(X40,X40) = k1_tarski(X40) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_81,plain,(
    ! [X41,X42] : k1_enumset1(X41,X41,X42) = k2_tarski(X41,X42) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_82,plain,(
    ! [X43,X44,X45] : k2_enumset1(X43,X43,X44,X45) = k1_enumset1(X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_83,plain,(
    ! [X46,X47,X48,X49] : k3_enumset1(X46,X46,X47,X48,X49) = k2_enumset1(X46,X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_84,plain,(
    ! [X50,X51,X52,X53,X54] : k4_enumset1(X50,X50,X51,X52,X53,X54) = k3_enumset1(X50,X51,X52,X53,X54) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_85,plain,(
    ! [X55,X56,X57,X58,X59,X60] : k5_enumset1(X55,X55,X56,X57,X58,X59,X60) = k4_enumset1(X55,X56,X57,X58,X59,X60) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_86,plain,(
    ! [X61,X62,X63,X64,X65,X66,X67] : k6_enumset1(X61,X61,X62,X63,X64,X65,X66,X67) = k5_enumset1(X61,X62,X63,X64,X65,X66,X67) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_87,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_71])])])).

cnf(c_0_88,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_70,c_0_31])).

cnf(c_0_89,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),k5_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_62]),c_0_72]),c_0_73]),c_0_50]),c_0_56])).

cnf(c_0_90,plain,
    ( k3_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),X2),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_77]),c_0_34]),c_0_76]),c_0_76]),c_0_77]),c_0_78]),c_0_64])).

cnf(c_0_91,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_92,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_93,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_94,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_95,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_96,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_97,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_98,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_99,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

fof(c_0_100,plain,(
    ! [X25,X26,X27,X28,X29,X30,X31,X32,X33,X34] :
      ( ( ~ r2_hidden(X29,X28)
        | X29 = X25
        | X29 = X26
        | X29 = X27
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( X30 != X25
        | r2_hidden(X30,X28)
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( X30 != X26
        | r2_hidden(X30,X28)
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( X30 != X27
        | r2_hidden(X30,X28)
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( esk1_4(X31,X32,X33,X34) != X31
        | ~ r2_hidden(esk1_4(X31,X32,X33,X34),X34)
        | X34 = k1_enumset1(X31,X32,X33) )
      & ( esk1_4(X31,X32,X33,X34) != X32
        | ~ r2_hidden(esk1_4(X31,X32,X33,X34),X34)
        | X34 = k1_enumset1(X31,X32,X33) )
      & ( esk1_4(X31,X32,X33,X34) != X33
        | ~ r2_hidden(esk1_4(X31,X32,X33,X34),X34)
        | X34 = k1_enumset1(X31,X32,X33) )
      & ( r2_hidden(esk1_4(X31,X32,X33,X34),X34)
        | esk1_4(X31,X32,X33,X34) = X31
        | esk1_4(X31,X32,X33,X34) = X32
        | esk1_4(X31,X32,X33,X34) = X33
        | X34 = k1_enumset1(X31,X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_101,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_88,c_0_50])).

cnf(c_0_102,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),X2),X2) = X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_75]),c_0_76]),c_0_77]),c_0_34]),c_0_64]),c_0_90]),c_0_34])).

cnf(c_0_103,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4)),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92]),c_0_93]),c_0_94]),c_0_94]),c_0_95]),c_0_95]),c_0_95]),c_0_25]),c_0_96]),c_0_96]),c_0_96]),c_0_96]),c_0_96]),c_0_97]),c_0_97]),c_0_97]),c_0_97]),c_0_97]),c_0_98]),c_0_98]),c_0_98]),c_0_98]),c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_92]),c_0_92]),c_0_92]),c_0_93]),c_0_93]),c_0_93]),c_0_94]),c_0_94]),c_0_94]),c_0_95]),c_0_95]),c_0_95]),c_0_96]),c_0_96]),c_0_96]),c_0_97]),c_0_97]),c_0_97]),c_0_98]),c_0_98]),c_0_98])).

cnf(c_0_105,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_106,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),X2) = X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_64]),c_0_90]),c_0_34]),c_0_75]),c_0_102])).

cnf(c_0_107,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(X1,X2),X2),k3_xboole_0(k3_xboole_0(X1,X2),X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_64])).

cnf(c_0_108,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) = k3_xboole_0(k5_xboole_0(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_104])).

cnf(c_0_111,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_112,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_94]),c_0_95]),c_0_96]),c_0_97]),c_0_98])).

cnf(c_0_113,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X1),X1)) = k3_xboole_0(k3_xboole_0(X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_55]),c_0_50]),c_0_106]),c_0_54])).

cnf(c_0_114,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_104]),c_0_108])).

cnf(c_0_115,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_108]),c_0_108])).

cnf(c_0_116,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_94]),c_0_95]),c_0_96]),c_0_97]),c_0_98])).

cnf(c_0_117,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_112])).

cnf(c_0_118,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_114]),c_0_115]),c_0_114])).

cnf(c_0_119,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4) ),
    inference(er,[status(thm)],[c_0_116])).

cnf(c_0_120,negated_conjecture,
    ( X1 = esk3_0
    | ~ r2_hidden(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_121,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[c_0_119])).

cnf(c_0_122,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_123,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_122]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:24:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.54  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.20/0.54  # and selection function SelectNegativeLiterals.
% 0.20/0.54  #
% 0.20/0.54  # Preprocessing time       : 0.026 s
% 0.20/0.54  
% 0.20/0.54  # Proof found!
% 0.20/0.54  # SZS status Theorem
% 0.20/0.54  # SZS output start CNFRefutation
% 0.20/0.54  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.20/0.54  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.20/0.54  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.54  fof(t93_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 0.20/0.54  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.54  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.20/0.54  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.20/0.54  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.20/0.54  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.20/0.54  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 0.20/0.54  fof(t18_zfmisc_1, conjecture, ![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 0.20/0.54  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 0.20/0.54  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.54  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.54  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.54  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.54  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.54  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.54  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.54  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.20/0.54  fof(c_0_20, plain, ![X23, X24]:k3_xboole_0(X23,X24)=k5_xboole_0(k5_xboole_0(X23,X24),k2_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.20/0.54  fof(c_0_21, plain, ![X21, X22]:k2_xboole_0(X21,X22)=k5_xboole_0(k5_xboole_0(X21,X22),k3_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.20/0.54  fof(c_0_22, plain, ![X8, X9]:k2_xboole_0(X8,X9)=k2_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.54  fof(c_0_23, plain, ![X19, X20]:k2_xboole_0(X19,X20)=k2_xboole_0(k5_xboole_0(X19,X20),k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t93_xboole_1])).
% 0.20/0.54  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.54  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.54  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.54  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.54  fof(c_0_28, plain, ![X17]:k3_xboole_0(X17,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.54  fof(c_0_29, plain, ![X18]:k5_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.20/0.54  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.54  cnf(c_0_31, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_25]), c_0_25])).
% 0.20/0.54  cnf(c_0_32, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_25]), c_0_25])).
% 0.20/0.54  cnf(c_0_33, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.54  cnf(c_0_34, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.54  fof(c_0_35, plain, ![X15, X16]:k3_xboole_0(X15,k2_xboole_0(X15,X16))=X15, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.20/0.54  cnf(c_0_36, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1)))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.54  cnf(c_0_37, plain, (k5_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_32, c_0_31])).
% 0.20/0.54  cnf(c_0_38, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_33]), c_0_34]), c_0_34]), c_0_34])).
% 0.20/0.54  cnf(c_0_39, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.54  cnf(c_0_40, plain, (k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.20/0.54  cnf(c_0_41, plain, (k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_39, c_0_25])).
% 0.20/0.54  fof(c_0_42, plain, ![X10]:k2_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.20/0.54  cnf(c_0_43, plain, (k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.54  cnf(c_0_44, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.54  fof(c_0_45, plain, ![X11]:k3_xboole_0(X11,X11)=X11, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.20/0.54  cnf(c_0_46, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_40]), c_0_34]), c_0_30])).
% 0.20/0.54  cnf(c_0_47, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_44, c_0_25])).
% 0.20/0.54  cnf(c_0_48, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.54  cnf(c_0_49, plain, (k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1)))=X1), inference(spm,[status(thm)],[c_0_41, c_0_31])).
% 0.20/0.54  cnf(c_0_50, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_46]), c_0_34])).
% 0.20/0.54  cnf(c_0_51, plain, (k5_xboole_0(k5_xboole_0(X1,X1),X1)=X1), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.54  fof(c_0_52, plain, ![X12, X13, X14]:k5_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(X14,X13))=k3_xboole_0(k5_xboole_0(X12,X14),X13), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 0.20/0.54  cnf(c_0_53, plain, (k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.54  cnf(c_0_54, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[c_0_51, c_0_38])).
% 0.20/0.54  cnf(c_0_55, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.54  cnf(c_0_56, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_50])).
% 0.20/0.54  cnf(c_0_57, plain, (k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_46]), c_0_54])).
% 0.20/0.54  cnf(c_0_58, plain, (k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))),X2)=k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_55, c_0_41])).
% 0.20/0.54  cnf(c_0_59, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_56]), c_0_56]), c_0_50])).
% 0.20/0.54  cnf(c_0_60, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_50]), c_0_50])).
% 0.20/0.54  cnf(c_0_61, plain, (k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),X3),k3_xboole_0(X1,X2))=k3_xboole_0(X3,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_40]), c_0_54])).
% 0.20/0.54  cnf(c_0_62, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X2,X1)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_50])).
% 0.20/0.54  cnf(c_0_63, plain, (k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_41, c_0_50])).
% 0.20/0.54  cnf(c_0_64, plain, (k5_xboole_0(k3_xboole_0(X1,X2),X2)=k3_xboole_0(k5_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_55, c_0_48])).
% 0.20/0.54  cnf(c_0_65, plain, (k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),X3),k5_xboole_0(X1,X2))=k3_xboole_0(X3,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_46]), c_0_54])).
% 0.20/0.54  cnf(c_0_66, plain, (k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))),X2)=k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_50]), c_0_50])).
% 0.20/0.54  cnf(c_0_67, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X2,X1)))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.54  cnf(c_0_68, plain, (k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_48])).
% 0.20/0.54  cnf(c_0_69, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X2,X1)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_60]), c_0_46]), c_0_54])).
% 0.20/0.54  cnf(c_0_70, plain, (k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1)),X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_64]), c_0_55])).
% 0.20/0.54  fof(c_0_71, negated_conjecture, ~(![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t18_zfmisc_1])).
% 0.20/0.54  cnf(c_0_72, plain, (k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),k5_xboole_0(X2,X1))=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_60]), c_0_48])).
% 0.20/0.54  cnf(c_0_73, plain, (k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X2,X1)))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_66, c_0_53])).
% 0.20/0.54  cnf(c_0_74, plain, (k5_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),k3_xboole_0(X2,X1))=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_67]), c_0_68]), c_0_69]), c_0_59])).
% 0.20/0.54  cnf(c_0_75, plain, (k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X2,X1)),X1))=X1), inference(rw,[status(thm)],[c_0_70, c_0_50])).
% 0.20/0.54  cnf(c_0_76, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(k5_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_55, c_0_48])).
% 0.20/0.54  cnf(c_0_77, plain, (k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X2,X1))),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_53])).
% 0.20/0.54  cnf(c_0_78, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_38]), c_0_38])).
% 0.20/0.54  fof(c_0_79, plain, ![X36, X37, X38, X39]:k2_enumset1(X36,X37,X38,X39)=k2_xboole_0(k1_enumset1(X36,X37,X38),k1_tarski(X39)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.20/0.54  fof(c_0_80, plain, ![X40]:k2_tarski(X40,X40)=k1_tarski(X40), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.54  fof(c_0_81, plain, ![X41, X42]:k1_enumset1(X41,X41,X42)=k2_tarski(X41,X42), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.54  fof(c_0_82, plain, ![X43, X44, X45]:k2_enumset1(X43,X43,X44,X45)=k1_enumset1(X43,X44,X45), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.54  fof(c_0_83, plain, ![X46, X47, X48, X49]:k3_enumset1(X46,X46,X47,X48,X49)=k2_enumset1(X46,X47,X48,X49), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.54  fof(c_0_84, plain, ![X50, X51, X52, X53, X54]:k4_enumset1(X50,X50,X51,X52,X53,X54)=k3_enumset1(X50,X51,X52,X53,X54), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.54  fof(c_0_85, plain, ![X55, X56, X57, X58, X59, X60]:k5_enumset1(X55,X55,X56,X57,X58,X59,X60)=k4_enumset1(X55,X56,X57,X58,X59,X60), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.54  fof(c_0_86, plain, ![X61, X62, X63, X64, X65, X66, X67]:k6_enumset1(X61,X61,X62,X63,X64,X65,X66,X67)=k5_enumset1(X61,X62,X63,X64,X65,X66,X67), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.54  fof(c_0_87, negated_conjecture, (k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)&esk2_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_71])])])).
% 0.20/0.54  cnf(c_0_88, plain, (k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X1))=X1), inference(spm,[status(thm)],[c_0_70, c_0_31])).
% 0.20/0.54  cnf(c_0_89, plain, (k5_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),k5_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_62]), c_0_72]), c_0_73]), c_0_50]), c_0_56])).
% 0.20/0.54  cnf(c_0_90, plain, (k3_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),X2),X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76]), c_0_77]), c_0_34]), c_0_76]), c_0_76]), c_0_77]), c_0_78]), c_0_64])).
% 0.20/0.54  cnf(c_0_91, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.54  cnf(c_0_92, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.54  cnf(c_0_93, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.54  cnf(c_0_94, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.20/0.54  cnf(c_0_95, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.20/0.54  cnf(c_0_96, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.20/0.54  cnf(c_0_97, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.20/0.54  cnf(c_0_98, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.20/0.54  cnf(c_0_99, negated_conjecture, (k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.20/0.54  fof(c_0_100, plain, ![X25, X26, X27, X28, X29, X30, X31, X32, X33, X34]:(((~r2_hidden(X29,X28)|(X29=X25|X29=X26|X29=X27)|X28!=k1_enumset1(X25,X26,X27))&(((X30!=X25|r2_hidden(X30,X28)|X28!=k1_enumset1(X25,X26,X27))&(X30!=X26|r2_hidden(X30,X28)|X28!=k1_enumset1(X25,X26,X27)))&(X30!=X27|r2_hidden(X30,X28)|X28!=k1_enumset1(X25,X26,X27))))&((((esk1_4(X31,X32,X33,X34)!=X31|~r2_hidden(esk1_4(X31,X32,X33,X34),X34)|X34=k1_enumset1(X31,X32,X33))&(esk1_4(X31,X32,X33,X34)!=X32|~r2_hidden(esk1_4(X31,X32,X33,X34),X34)|X34=k1_enumset1(X31,X32,X33)))&(esk1_4(X31,X32,X33,X34)!=X33|~r2_hidden(esk1_4(X31,X32,X33,X34),X34)|X34=k1_enumset1(X31,X32,X33)))&(r2_hidden(esk1_4(X31,X32,X33,X34),X34)|(esk1_4(X31,X32,X33,X34)=X31|esk1_4(X31,X32,X33,X34)=X32|esk1_4(X31,X32,X33,X34)=X33)|X34=k1_enumset1(X31,X32,X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.20/0.54  cnf(c_0_101, plain, (k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),X1))=X1), inference(rw,[status(thm)],[c_0_88, c_0_50])).
% 0.20/0.54  cnf(c_0_102, plain, (k3_xboole_0(k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),X2),X2)=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_75]), c_0_76]), c_0_77]), c_0_34]), c_0_64]), c_0_90]), c_0_34])).
% 0.20/0.54  cnf(c_0_103, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4)),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_92]), c_0_93]), c_0_94]), c_0_94]), c_0_95]), c_0_95]), c_0_95]), c_0_25]), c_0_96]), c_0_96]), c_0_96]), c_0_96]), c_0_96]), c_0_97]), c_0_97]), c_0_97]), c_0_97]), c_0_97]), c_0_98]), c_0_98]), c_0_98]), c_0_98]), c_0_98])).
% 0.20/0.54  cnf(c_0_104, negated_conjecture, (k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_92]), c_0_92]), c_0_92]), c_0_93]), c_0_93]), c_0_93]), c_0_94]), c_0_94]), c_0_94]), c_0_95]), c_0_95]), c_0_95]), c_0_96]), c_0_96]), c_0_96]), c_0_97]), c_0_97]), c_0_97]), c_0_98]), c_0_98]), c_0_98])).
% 0.20/0.54  cnf(c_0_105, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.20/0.54  cnf(c_0_106, plain, (k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)),X2)=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_64]), c_0_90]), c_0_34]), c_0_75]), c_0_102])).
% 0.20/0.54  cnf(c_0_107, plain, (k3_xboole_0(k3_xboole_0(k5_xboole_0(X1,X2),X2),k3_xboole_0(k3_xboole_0(X1,X2),X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_64])).
% 0.20/0.54  cnf(c_0_108, negated_conjecture, (k5_xboole_0(k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.20/0.54  cnf(c_0_109, negated_conjecture, (k5_xboole_0(k3_xboole_0(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))=k3_xboole_0(k5_xboole_0(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_55, c_0_104])).
% 0.20/0.54  cnf(c_0_110, negated_conjecture, (k3_xboole_0(k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_64, c_0_104])).
% 0.20/0.54  cnf(c_0_111, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.20/0.54  cnf(c_0_112, plain, (X1=X5|X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_94]), c_0_95]), c_0_96]), c_0_97]), c_0_98])).
% 0.20/0.54  cnf(c_0_113, plain, (k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X1),X1))=k3_xboole_0(k3_xboole_0(X2,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_55]), c_0_50]), c_0_106]), c_0_54])).
% 0.20/0.54  cnf(c_0_114, negated_conjecture, (k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_104]), c_0_108])).
% 0.20/0.54  cnf(c_0_115, negated_conjecture, (k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_108]), c_0_108])).
% 0.20/0.54  cnf(c_0_116, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_94]), c_0_95]), c_0_96]), c_0_97]), c_0_98])).
% 0.20/0.54  cnf(c_0_117, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_112])).
% 0.20/0.54  cnf(c_0_118, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_114]), c_0_115]), c_0_114])).
% 0.20/0.54  cnf(c_0_119, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4)), inference(er,[status(thm)],[c_0_116])).
% 0.20/0.54  cnf(c_0_120, negated_conjecture, (X1=esk3_0|~r2_hidden(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 0.20/0.54  cnf(c_0_121, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3))), inference(er,[status(thm)],[c_0_119])).
% 0.20/0.54  cnf(c_0_122, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.20/0.54  cnf(c_0_123, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_122]), ['proof']).
% 0.20/0.54  # SZS output end CNFRefutation
% 0.20/0.54  # Proof object total steps             : 124
% 0.20/0.54  # Proof object clause steps            : 83
% 0.20/0.54  # Proof object formula steps           : 41
% 0.20/0.54  # Proof object conjectures             : 14
% 0.20/0.54  # Proof object clause conjectures      : 11
% 0.20/0.54  # Proof object formula conjectures     : 3
% 0.20/0.54  # Proof object initial clauses used    : 22
% 0.20/0.54  # Proof object initial formulas used   : 20
% 0.20/0.54  # Proof object generating inferences   : 39
% 0.20/0.54  # Proof object simplifying inferences  : 132
% 0.20/0.54  # Training examples: 0 positive, 0 negative
% 0.20/0.54  # Parsed axioms                        : 20
% 0.20/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.54  # Initial clauses                      : 28
% 0.20/0.54  # Removed in clause preprocessing      : 8
% 0.20/0.54  # Initial clauses in saturation        : 20
% 0.20/0.54  # Processed clauses                    : 250
% 0.20/0.54  # ...of these trivial                  : 73
% 0.20/0.54  # ...subsumed                          : 1
% 0.20/0.54  # ...remaining for further processing  : 176
% 0.20/0.54  # Other redundant clauses eliminated   : 30
% 0.20/0.54  # Clauses deleted for lack of memory   : 0
% 0.20/0.54  # Backward-subsumed                    : 0
% 0.20/0.54  # Backward-rewritten                   : 68
% 0.20/0.54  # Generated clauses                    : 13847
% 0.20/0.54  # ...of the previous two non-trivial   : 10130
% 0.20/0.54  # Contextual simplify-reflections      : 0
% 0.20/0.54  # Paramodulations                      : 13809
% 0.20/0.54  # Factorizations                       : 2
% 0.20/0.54  # Equation resolutions                 : 36
% 0.20/0.54  # Propositional unsat checks           : 0
% 0.20/0.54  #    Propositional check models        : 0
% 0.20/0.54  #    Propositional check unsatisfiable : 0
% 0.20/0.54  #    Propositional clauses             : 0
% 0.20/0.54  #    Propositional clauses after purity: 0
% 0.20/0.54  #    Propositional unsat core size     : 0
% 0.20/0.54  #    Propositional preprocessing time  : 0.000
% 0.20/0.54  #    Propositional encoding time       : 0.000
% 0.20/0.54  #    Propositional solver time         : 0.000
% 0.20/0.54  #    Success case prop preproc time    : 0.000
% 0.20/0.54  #    Success case prop encoding time   : 0.000
% 0.20/0.54  #    Success case prop solver time     : 0.000
% 0.20/0.54  # Current number of processed clauses  : 105
% 0.20/0.54  #    Positive orientable unit clauses  : 89
% 0.20/0.54  #    Positive unorientable unit clauses: 1
% 0.20/0.54  #    Negative unit clauses             : 1
% 0.20/0.54  #    Non-unit-clauses                  : 14
% 0.20/0.54  # Current number of unprocessed clauses: 9817
% 0.20/0.54  # ...number of literals in the above   : 21218
% 0.20/0.54  # Current number of archived formulas  : 0
% 0.20/0.54  # Current number of archived clauses   : 76
% 0.20/0.54  # Clause-clause subsumption calls (NU) : 71
% 0.20/0.54  # Rec. Clause-clause subsumption calls : 48
% 0.20/0.54  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.54  # Unit Clause-clause subsumption calls : 12
% 0.20/0.54  # Rewrite failures with RHS unbound    : 0
% 0.20/0.54  # BW rewrite match attempts            : 280
% 0.20/0.54  # BW rewrite match successes           : 31
% 0.20/0.54  # Condensation attempts                : 0
% 0.20/0.54  # Condensation successes               : 0
% 0.20/0.54  # Termbank termtop insertions          : 487484
% 0.20/0.54  
% 0.20/0.54  # -------------------------------------------------
% 0.20/0.54  # User time                : 0.200 s
% 0.20/0.54  # System time              : 0.010 s
% 0.20/0.54  # Total time               : 0.210 s
% 0.20/0.54  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
