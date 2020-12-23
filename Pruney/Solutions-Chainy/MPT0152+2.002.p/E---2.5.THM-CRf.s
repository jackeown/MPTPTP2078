%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:28 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   98 (36004 expanded)
%              Number of clauses        :   65 (16391 expanded)
%              Number of leaves         :   16 (9806 expanded)
%              Depth                    :   21
%              Number of atoms          :   98 (36004 expanded)
%              Number of equality atoms :   97 (36003 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(l68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(t57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t5_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_1)).

fof(t62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(t56_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(t65_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_enumset1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(t68_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(c_0_16,plain,(
    ! [X26,X27,X28] : k1_enumset1(X26,X27,X28) = k2_xboole_0(k1_tarski(X26),k2_tarski(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_17,plain,(
    ! [X24,X25] : k2_tarski(X24,X25) = k2_xboole_0(k1_tarski(X24),k1_tarski(X25)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_18,plain,(
    ! [X29,X30,X31,X32,X33] : k3_enumset1(X29,X30,X31,X32,X33) = k2_xboole_0(k2_tarski(X29,X30),k1_enumset1(X31,X32,X33)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23] : k5_enumset1(X17,X18,X19,X20,X21,X22,X23) = k2_xboole_0(k2_enumset1(X17,X18,X19,X20),k1_enumset1(X21,X22,X23)) ),
    inference(variable_rename,[status(thm)],[l68_enumset1])).

fof(c_0_22,plain,(
    ! [X39,X40,X41,X42,X43,X44] : k4_enumset1(X39,X40,X41,X42,X43,X44) = k2_xboole_0(k1_tarski(X39),k3_enumset1(X40,X41,X42,X43,X44)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

cnf(c_0_23,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_25,plain,(
    ! [X58,X59,X60,X61,X62,X63,X64] : k5_enumset1(X58,X59,X60,X61,X62,X63,X64) = k2_xboole_0(k2_tarski(X58,X59),k3_enumset1(X60,X61,X62,X63,X64)) ),
    inference(variable_rename,[status(thm)],[t57_enumset1])).

cnf(c_0_26,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X34,X35,X36,X37,X38] : k3_enumset1(X34,X35,X36,X37,X38) = k2_xboole_0(k2_enumset1(X34,X35,X36,X37),k1_tarski(X38)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

fof(c_0_28,plain,(
    ! [X15,X16] : k2_xboole_0(X15,k2_xboole_0(X15,X16)) = k2_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

fof(c_0_29,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_30,plain,(
    ! [X12,X13,X14] : k2_xboole_0(k2_xboole_0(X12,X13),X14) = k2_xboole_0(k2_xboole_0(X12,X14),k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t5_xboole_1])).

fof(c_0_31,plain,(
    ! [X65,X66,X67,X68,X69,X70,X71,X72] : k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72) = k2_xboole_0(k1_tarski(X65),k5_enumset1(X66,X67,X68,X69,X70,X71,X72)) ),
    inference(variable_rename,[status(thm)],[t62_enumset1])).

fof(c_0_32,plain,(
    ! [X51,X52,X53,X54,X55,X56,X57] : k5_enumset1(X51,X52,X53,X54,X55,X56,X57) = k2_xboole_0(k1_tarski(X51),k4_enumset1(X52,X53,X54,X55,X56,X57)) ),
    inference(variable_rename,[status(thm)],[t56_enumset1])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_20]),c_0_24])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7)))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_41,plain,(
    ! [X73,X74,X75,X76,X77,X78,X79,X80] : k6_enumset1(X73,X74,X75,X76,X77,X78,X79,X80) = k2_xboole_0(k2_enumset1(X73,X74,X75,X76),k2_enumset1(X77,X78,X79,X80)) ),
    inference(variable_rename,[status(thm)],[t65_enumset1])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_45,plain,
    ( k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X4)),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_20]),c_0_34]),c_0_36])).

cnf(c_0_46,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_34])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k2_xboole_0(k2_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_49,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k1_tarski(X7),k1_tarski(X8))))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_36])).

cnf(c_0_51,plain,
    ( k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7)))) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X4)),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_36])).

cnf(c_0_52,plain,
    ( k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_47]),c_0_47]),c_0_48])).

cnf(c_0_54,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k1_tarski(X7),k1_tarski(X8))))) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7))) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_46]),c_0_52])).

fof(c_0_56,plain,(
    ! [X11] : k2_xboole_0(X11,X11) = X11 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_57,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_53])).

cnf(c_0_58,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_enumset1(X4,X5,X6,X7),k1_tarski(X8))))) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_52]),c_0_55])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_60,plain,
    ( k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X1,X2,X3,X5)) = k2_xboole_0(k2_enumset1(X4,X1,X2,X3),k1_tarski(X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_57]),c_0_53]),c_0_53]),c_0_53]),c_0_47]),c_0_58])).

fof(c_0_61,plain,(
    ! [X45,X46,X47,X48,X49,X50] : k4_enumset1(X45,X46,X47,X48,X49,X50) = k2_xboole_0(k3_enumset1(X45,X46,X47,X48,X49),k1_tarski(X50)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

cnf(c_0_62,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_enumset1(X1,X2,X3,X4)) = k2_enumset1(X2,X3,X4,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_39])).

cnf(c_0_63,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_64,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X1)) = k2_enumset1(X2,X3,X4,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_62])).

cnf(c_0_65,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))),k1_tarski(X6)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_34]),c_0_44])).

cnf(c_0_66,plain,
    ( k2_enumset1(X1,X2,X3,X1) = k2_enumset1(X2,X3,X1,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_64])).

cnf(c_0_67,plain,
    ( k2_xboole_0(k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)),k1_tarski(X6)) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_46]),c_0_46])).

fof(c_0_68,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(assume_negation,[status(cth)],[t68_enumset1])).

cnf(c_0_69,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X1,X3,X2)) = k2_enumset1(X3,X2,X2,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_66])).

cnf(c_0_70,plain,
    ( k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7)))) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7)))) ),
    inference(rw,[status(thm)],[c_0_52,c_0_55])).

cnf(c_0_71,plain,
    ( k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6))) ),
    inference(rw,[status(thm)],[c_0_67,c_0_53])).

cnf(c_0_72,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_47]),c_0_53]),c_0_53])).

fof(c_0_73,negated_conjecture,(
    k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_68])])])).

cnf(c_0_74,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),X5)) = k2_xboole_0(k2_enumset1(X2,X3,X4,X1),X5) ),
    inference(spm,[status(thm)],[c_0_53,c_0_62])).

cnf(c_0_75,plain,
    ( k2_xboole_0(k2_enumset1(X1,X2,X3,X1),k2_enumset1(X3,X1,X1,X2)) = k2_enumset1(X3,X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_69])).

cnf(c_0_76,plain,
    ( k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X2,X3,X4,X1)) = k2_enumset1(X2,X3,X4,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_62])).

cnf(c_0_77,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6))) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_enumset1(X3,X4,X5,X6))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_59]),c_0_39]),c_0_64]),c_0_71])).

cnf(c_0_78,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_xboole_0(X2,k2_enumset1(X3,X4,X5,X1))) = k2_xboole_0(X2,k2_enumset1(X3,X4,X5,X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_62])).

cnf(c_0_79,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X1,X1,X3)) = k2_enumset1(X2,X1,X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_81,plain,
    ( k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_77]),c_0_78])).

cnf(c_0_82,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X1,X4)) = k2_enumset1(X2,X3,X1,X4) ),
    inference(spm,[status(thm)],[c_0_78,c_0_62])).

cnf(c_0_83,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),k2_xboole_0(k1_tarski(esk6_0),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0))))) != k2_xboole_0(k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk6_0),k1_tarski(esk7_0)))),k1_tarski(esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_36]),c_0_50])).

cnf(c_0_84,plain,
    ( k2_enumset1(X1,X2,X2,X1) = k2_enumset1(X1,X1,X2,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_66]),c_0_62])).

cnf(c_0_85,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X3,X4)) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_66]),c_0_81]),c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk8_0),k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk6_0),k1_tarski(esk7_0))))) != k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),k2_xboole_0(k1_tarski(esk6_0),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0))))) ),
    inference(rw,[status(thm)],[c_0_83,c_0_39])).

cnf(c_0_87,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k2_enumset1(X1,X1,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_84]),c_0_81]),c_0_82]),c_0_62])).

cnf(c_0_88,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X2,X3,X4)) = k2_enumset1(X4,X1,X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_85]),c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( k2_xboole_0(k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0),k2_enumset1(esk8_0,esk1_0,esk2_0,esk3_0)) != k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_54]),c_0_39]),c_0_54])).

cnf(c_0_90,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X1,X3,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_87]),c_0_81]),c_0_62]),c_0_62])).

cnf(c_0_91,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X1,X3,X4)) = k2_enumset1(X2,X1,X3,X4) ),
    inference(spm,[status(thm)],[c_0_38,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( k2_xboole_0(k2_enumset1(esk1_0,esk8_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0)) != k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90]),c_0_39])).

cnf(c_0_93,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X4,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_90]),c_0_91])).

cnf(c_0_94,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k2_enumset1(X5,X6,X7,X8))))) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_77])).

cnf(c_0_95,negated_conjecture,
    ( k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk8_0),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0)) != k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93]),c_0_93])).

cnf(c_0_96,plain,
    ( k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k2_xboole_0(k2_enumset1(X1,X2,X3,X8),k2_enumset1(X4,X5,X6,X7)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_39]),c_0_77]),c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.66/1.83  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.66/1.83  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.66/1.83  #
% 1.66/1.83  # Preprocessing time       : 0.027 s
% 1.66/1.83  # Presaturation interreduction done
% 1.66/1.83  
% 1.66/1.83  # Proof found!
% 1.66/1.83  # SZS status Theorem
% 1.66/1.83  # SZS output start CNFRefutation
% 1.66/1.83  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 1.66/1.83  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.66/1.83  fof(t48_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 1.66/1.83  fof(l68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 1.66/1.83  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 1.66/1.83  fof(t57_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 1.66/1.83  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 1.66/1.83  fof(t6_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 1.66/1.83  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.66/1.83  fof(t5_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_xboole_1)).
% 1.66/1.83  fof(t62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 1.66/1.83  fof(t56_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 1.66/1.83  fof(t65_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_enumset1)).
% 1.66/1.83  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.66/1.83  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 1.66/1.83  fof(t68_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 1.66/1.83  fof(c_0_16, plain, ![X26, X27, X28]:k1_enumset1(X26,X27,X28)=k2_xboole_0(k1_tarski(X26),k2_tarski(X27,X28)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 1.66/1.83  fof(c_0_17, plain, ![X24, X25]:k2_tarski(X24,X25)=k2_xboole_0(k1_tarski(X24),k1_tarski(X25)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 1.66/1.83  fof(c_0_18, plain, ![X29, X30, X31, X32, X33]:k3_enumset1(X29,X30,X31,X32,X33)=k2_xboole_0(k2_tarski(X29,X30),k1_enumset1(X31,X32,X33)), inference(variable_rename,[status(thm)],[t48_enumset1])).
% 1.66/1.83  cnf(c_0_19, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.66/1.83  cnf(c_0_20, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.66/1.83  fof(c_0_21, plain, ![X17, X18, X19, X20, X21, X22, X23]:k5_enumset1(X17,X18,X19,X20,X21,X22,X23)=k2_xboole_0(k2_enumset1(X17,X18,X19,X20),k1_enumset1(X21,X22,X23)), inference(variable_rename,[status(thm)],[l68_enumset1])).
% 1.66/1.83  fof(c_0_22, plain, ![X39, X40, X41, X42, X43, X44]:k4_enumset1(X39,X40,X41,X42,X43,X44)=k2_xboole_0(k1_tarski(X39),k3_enumset1(X40,X41,X42,X43,X44)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 1.66/1.83  cnf(c_0_23, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.66/1.83  cnf(c_0_24, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 1.66/1.83  fof(c_0_25, plain, ![X58, X59, X60, X61, X62, X63, X64]:k5_enumset1(X58,X59,X60,X61,X62,X63,X64)=k2_xboole_0(k2_tarski(X58,X59),k3_enumset1(X60,X61,X62,X63,X64)), inference(variable_rename,[status(thm)],[t57_enumset1])).
% 1.66/1.83  cnf(c_0_26, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.66/1.83  fof(c_0_27, plain, ![X34, X35, X36, X37, X38]:k3_enumset1(X34,X35,X36,X37,X38)=k2_xboole_0(k2_enumset1(X34,X35,X36,X37),k1_tarski(X38)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 1.66/1.83  fof(c_0_28, plain, ![X15, X16]:k2_xboole_0(X15,k2_xboole_0(X15,X16))=k2_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t6_xboole_1])).
% 1.66/1.83  fof(c_0_29, plain, ![X9, X10]:k2_xboole_0(X9,X10)=k2_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.66/1.83  fof(c_0_30, plain, ![X12, X13, X14]:k2_xboole_0(k2_xboole_0(X12,X13),X14)=k2_xboole_0(k2_xboole_0(X12,X14),k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t5_xboole_1])).
% 1.66/1.83  fof(c_0_31, plain, ![X65, X66, X67, X68, X69, X70, X71, X72]:k6_enumset1(X65,X66,X67,X68,X69,X70,X71,X72)=k2_xboole_0(k1_tarski(X65),k5_enumset1(X66,X67,X68,X69,X70,X71,X72)), inference(variable_rename,[status(thm)],[t62_enumset1])).
% 1.66/1.83  fof(c_0_32, plain, ![X51, X52, X53, X54, X55, X56, X57]:k5_enumset1(X51,X52,X53,X54,X55,X56,X57)=k2_xboole_0(k1_tarski(X51),k4_enumset1(X52,X53,X54,X55,X56,X57)), inference(variable_rename,[status(thm)],[t56_enumset1])).
% 1.66/1.83  cnf(c_0_33, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.66/1.83  cnf(c_0_34, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_20]), c_0_24])).
% 1.66/1.83  cnf(c_0_35, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.66/1.83  cnf(c_0_36, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))), inference(rw,[status(thm)],[c_0_26, c_0_24])).
% 1.66/1.83  cnf(c_0_37, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.66/1.83  cnf(c_0_38, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.66/1.83  cnf(c_0_39, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.66/1.83  cnf(c_0_40, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.66/1.83  fof(c_0_41, plain, ![X73, X74, X75, X76, X77, X78, X79, X80]:k6_enumset1(X73,X74,X75,X76,X77,X78,X79,X80)=k2_xboole_0(k2_enumset1(X73,X74,X75,X76),k2_enumset1(X77,X78,X79,X80)), inference(variable_rename,[status(thm)],[t65_enumset1])).
% 1.66/1.83  cnf(c_0_42, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.66/1.83  cnf(c_0_43, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.66/1.83  cnf(c_0_44, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 1.66/1.83  cnf(c_0_45, plain, (k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X4)),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_20]), c_0_34]), c_0_36])).
% 1.66/1.83  cnf(c_0_46, plain, (k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(rw,[status(thm)],[c_0_37, c_0_34])).
% 1.66/1.83  cnf(c_0_47, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.66/1.83  cnf(c_0_48, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))=k2_xboole_0(k2_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 1.66/1.83  cnf(c_0_49, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.66/1.83  cnf(c_0_50, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k1_tarski(X7),k1_tarski(X8)))))), inference(rw,[status(thm)],[c_0_42, c_0_36])).
% 1.66/1.83  cnf(c_0_51, plain, (k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X4)),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_36])).
% 1.66/1.83  cnf(c_0_52, plain, (k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7)))), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 1.66/1.83  cnf(c_0_53, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_47]), c_0_47]), c_0_48])).
% 1.66/1.83  cnf(c_0_54, plain, (k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k1_tarski(X7),k1_tarski(X8)))))=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 1.66/1.83  cnf(c_0_55, plain, (k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7)))=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_46]), c_0_52])).
% 1.66/1.83  fof(c_0_56, plain, ![X11]:k2_xboole_0(X11,X11)=X11, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 1.66/1.83  cnf(c_0_57, plain, (k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))))=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(rw,[status(thm)],[c_0_46, c_0_53])).
% 1.66/1.83  cnf(c_0_58, plain, (k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_enumset1(X4,X5,X6,X7),k1_tarski(X8)))))=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_52]), c_0_55])).
% 1.66/1.83  cnf(c_0_59, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 1.66/1.83  cnf(c_0_60, plain, (k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X1,X2,X3,X5))=k2_xboole_0(k2_enumset1(X4,X1,X2,X3),k1_tarski(X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_57]), c_0_53]), c_0_53]), c_0_53]), c_0_47]), c_0_58])).
% 1.66/1.83  fof(c_0_61, plain, ![X45, X46, X47, X48, X49, X50]:k4_enumset1(X45,X46,X47,X48,X49,X50)=k2_xboole_0(k3_enumset1(X45,X46,X47,X48,X49),k1_tarski(X50)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 1.66/1.83  cnf(c_0_62, plain, (k2_xboole_0(k1_tarski(X1),k2_enumset1(X1,X2,X3,X4))=k2_enumset1(X2,X3,X4,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_39])).
% 1.66/1.83  cnf(c_0_63, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.66/1.83  cnf(c_0_64, plain, (k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X1))=k2_enumset1(X2,X3,X4,X1)), inference(spm,[status(thm)],[c_0_38, c_0_62])).
% 1.66/1.83  cnf(c_0_65, plain, (k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))))=k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))),k1_tarski(X6))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_34]), c_0_44])).
% 1.66/1.83  cnf(c_0_66, plain, (k2_enumset1(X1,X2,X3,X1)=k2_enumset1(X2,X3,X1,X1)), inference(spm,[status(thm)],[c_0_62, c_0_64])).
% 1.66/1.83  cnf(c_0_67, plain, (k2_xboole_0(k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)),k1_tarski(X6))=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_46]), c_0_46])).
% 1.66/1.83  fof(c_0_68, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))), inference(assume_negation,[status(cth)],[t68_enumset1])).
% 1.66/1.83  cnf(c_0_69, plain, (k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X1,X3,X2))=k2_enumset1(X3,X2,X2,X1)), inference(spm,[status(thm)],[c_0_62, c_0_66])).
% 1.66/1.83  cnf(c_0_70, plain, (k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7))))), inference(rw,[status(thm)],[c_0_52, c_0_55])).
% 1.66/1.83  cnf(c_0_71, plain, (k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6)))), inference(rw,[status(thm)],[c_0_67, c_0_53])).
% 1.66/1.83  cnf(c_0_72, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_47]), c_0_53]), c_0_53])).
% 1.66/1.83  fof(c_0_73, negated_conjecture, k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_68])])])).
% 1.66/1.83  cnf(c_0_74, plain, (k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),X5))=k2_xboole_0(k2_enumset1(X2,X3,X4,X1),X5)), inference(spm,[status(thm)],[c_0_53, c_0_62])).
% 1.66/1.83  cnf(c_0_75, plain, (k2_xboole_0(k2_enumset1(X1,X2,X3,X1),k2_enumset1(X3,X1,X1,X2))=k2_enumset1(X3,X1,X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_69])).
% 1.66/1.83  cnf(c_0_76, plain, (k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X2,X3,X4,X1))=k2_enumset1(X2,X3,X4,X1)), inference(spm,[status(thm)],[c_0_47, c_0_62])).
% 1.66/1.83  cnf(c_0_77, plain, (k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6)))=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_enumset1(X3,X4,X5,X6)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_59]), c_0_39]), c_0_64]), c_0_71])).
% 1.66/1.83  cnf(c_0_78, plain, (k2_xboole_0(k1_tarski(X1),k2_xboole_0(X2,k2_enumset1(X3,X4,X5,X1)))=k2_xboole_0(X2,k2_enumset1(X3,X4,X5,X1))), inference(spm,[status(thm)],[c_0_72, c_0_62])).
% 1.66/1.83  cnf(c_0_79, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 1.66/1.83  cnf(c_0_80, plain, (k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X1,X1,X3))=k2_enumset1(X2,X1,X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 1.66/1.83  cnf(c_0_81, plain, (k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_77]), c_0_78])).
% 1.66/1.83  cnf(c_0_82, plain, (k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X1,X4))=k2_enumset1(X2,X3,X1,X4)), inference(spm,[status(thm)],[c_0_78, c_0_62])).
% 1.66/1.83  cnf(c_0_83, negated_conjecture, (k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),k2_xboole_0(k1_tarski(esk6_0),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0)))))!=k2_xboole_0(k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk6_0),k1_tarski(esk7_0)))),k1_tarski(esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_36]), c_0_50])).
% 1.66/1.83  cnf(c_0_84, plain, (k2_enumset1(X1,X2,X2,X1)=k2_enumset1(X1,X1,X2,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_66]), c_0_62])).
% 1.66/1.83  cnf(c_0_85, plain, (k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X3,X4))=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_66]), c_0_81]), c_0_82])).
% 1.66/1.83  cnf(c_0_86, negated_conjecture, (k2_xboole_0(k1_tarski(esk8_0),k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk6_0),k1_tarski(esk7_0)))))!=k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),k2_xboole_0(k1_tarski(esk6_0),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0)))))), inference(rw,[status(thm)],[c_0_83, c_0_39])).
% 1.66/1.83  cnf(c_0_87, plain, (k2_enumset1(X1,X1,X2,X3)=k2_enumset1(X1,X1,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_84]), c_0_81]), c_0_82]), c_0_62])).
% 1.66/1.83  cnf(c_0_88, plain, (k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X2,X3,X4))=k2_enumset1(X4,X1,X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_85]), c_0_81])).
% 1.66/1.83  cnf(c_0_89, negated_conjecture, (k2_xboole_0(k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0),k2_enumset1(esk8_0,esk1_0,esk2_0,esk3_0))!=k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_54]), c_0_39]), c_0_54])).
% 1.66/1.83  cnf(c_0_90, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X1,X3,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_87]), c_0_81]), c_0_62]), c_0_62])).
% 1.66/1.83  cnf(c_0_91, plain, (k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X1,X3,X4))=k2_enumset1(X2,X1,X3,X4)), inference(spm,[status(thm)],[c_0_38, c_0_88])).
% 1.66/1.83  cnf(c_0_92, negated_conjecture, (k2_xboole_0(k2_enumset1(esk1_0,esk8_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0))!=k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90]), c_0_39])).
% 1.66/1.83  cnf(c_0_93, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X1,X3,X4,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_90]), c_0_91])).
% 1.66/1.83  cnf(c_0_94, plain, (k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k2_enumset1(X5,X6,X7,X8)))))=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(rw,[status(thm)],[c_0_58, c_0_77])).
% 1.66/1.83  cnf(c_0_95, negated_conjecture, (k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk8_0),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0))!=k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93]), c_0_93])).
% 1.66/1.83  cnf(c_0_96, plain, (k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))=k2_xboole_0(k2_enumset1(X1,X2,X3,X8),k2_enumset1(X4,X5,X6,X7))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_39]), c_0_77]), c_0_94])).
% 1.66/1.83  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96])]), ['proof']).
% 1.66/1.83  # SZS output end CNFRefutation
% 1.66/1.83  # Proof object total steps             : 98
% 1.66/1.83  # Proof object clause steps            : 65
% 1.66/1.83  # Proof object formula steps           : 33
% 1.66/1.83  # Proof object conjectures             : 10
% 1.66/1.83  # Proof object clause conjectures      : 7
% 1.66/1.83  # Proof object formula conjectures     : 3
% 1.66/1.83  # Proof object initial clauses used    : 16
% 1.66/1.83  # Proof object initial formulas used   : 16
% 1.66/1.83  # Proof object generating inferences   : 25
% 1.66/1.83  # Proof object simplifying inferences  : 66
% 1.66/1.83  # Training examples: 0 positive, 0 negative
% 1.66/1.83  # Parsed axioms                        : 16
% 1.66/1.83  # Removed by relevancy pruning/SinE    : 0
% 1.66/1.83  # Initial clauses                      : 16
% 1.66/1.83  # Removed in clause preprocessing      : 6
% 1.66/1.83  # Initial clauses in saturation        : 10
% 1.66/1.83  # Processed clauses                    : 5044
% 1.66/1.83  # ...of these trivial                  : 2902
% 1.66/1.83  # ...subsumed                          : 1733
% 1.66/1.83  # ...remaining for further processing  : 409
% 1.66/1.83  # Other redundant clauses eliminated   : 0
% 1.66/1.83  # Clauses deleted for lack of memory   : 0
% 1.66/1.83  # Backward-subsumed                    : 22
% 1.66/1.83  # Backward-rewritten                   : 80
% 1.66/1.83  # Generated clauses                    : 159298
% 1.66/1.83  # ...of the previous two non-trivial   : 138021
% 1.66/1.83  # Contextual simplify-reflections      : 0
% 1.66/1.83  # Paramodulations                      : 159298
% 1.66/1.83  # Factorizations                       : 0
% 1.66/1.83  # Equation resolutions                 : 0
% 1.66/1.83  # Propositional unsat checks           : 0
% 1.66/1.83  #    Propositional check models        : 0
% 1.66/1.83  #    Propositional check unsatisfiable : 0
% 1.66/1.83  #    Propositional clauses             : 0
% 1.66/1.83  #    Propositional clauses after purity: 0
% 1.66/1.83  #    Propositional unsat core size     : 0
% 1.66/1.83  #    Propositional preprocessing time  : 0.000
% 1.66/1.83  #    Propositional encoding time       : 0.000
% 1.66/1.83  #    Propositional solver time         : 0.000
% 1.66/1.83  #    Success case prop preproc time    : 0.000
% 1.66/1.83  #    Success case prop encoding time   : 0.000
% 1.66/1.83  #    Success case prop solver time     : 0.000
% 1.66/1.83  # Current number of processed clauses  : 297
% 1.66/1.83  #    Positive orientable unit clauses  : 112
% 1.66/1.83  #    Positive unorientable unit clauses: 185
% 1.66/1.83  #    Negative unit clauses             : 0
% 1.66/1.83  #    Non-unit-clauses                  : 0
% 1.66/1.83  # Current number of unprocessed clauses: 130217
% 1.66/1.83  # ...number of literals in the above   : 130217
% 1.66/1.83  # Current number of archived formulas  : 0
% 1.66/1.83  # Current number of archived clauses   : 118
% 1.66/1.83  # Clause-clause subsumption calls (NU) : 0
% 1.66/1.83  # Rec. Clause-clause subsumption calls : 0
% 1.66/1.83  # Non-unit clause-clause subsumptions  : 0
% 1.66/1.83  # Unit Clause-clause subsumption calls : 13184
% 1.66/1.83  # Rewrite failures with RHS unbound    : 0
% 1.66/1.83  # BW rewrite match attempts            : 44560
% 1.66/1.83  # BW rewrite match successes           : 5714
% 1.66/1.83  # Condensation attempts                : 0
% 1.66/1.83  # Condensation successes               : 0
% 1.66/1.83  # Termbank termtop insertions          : 2617164
% 1.66/1.84  
% 1.66/1.84  # -------------------------------------------------
% 1.66/1.84  # User time                : 1.409 s
% 1.66/1.84  # System time              : 0.088 s
% 1.66/1.84  # Total time               : 1.497 s
% 1.66/1.84  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
