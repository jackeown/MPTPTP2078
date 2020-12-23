%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:30 EST 2020

% Result     : Theorem 33.83s
% Output     : CNFRefutation 33.83s
% Verified   : 
% Statistics : Number of formulae       :  147 (520863 expanded)
%              Number of clauses        :  110 (217722 expanded)
%              Number of leaves         :   18 (151570 expanded)
%              Depth                    :   27
%              Number of atoms          :  147 (520863 expanded)
%              Number of equality atoms :  146 (520862 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :   12 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t50_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t99_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k5_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t102_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k5_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(c_0_18,plain,(
    ! [X38,X39] : k4_xboole_0(X38,k4_xboole_0(X38,X39)) = k3_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_19,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_20,plain,(
    ! [X36,X37] : k4_xboole_0(X36,k3_xboole_0(X36,X37)) = k4_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_21,plain,(
    ! [X43,X44,X45] : k3_xboole_0(X43,k4_xboole_0(X44,X45)) = k4_xboole_0(k3_xboole_0(X43,X44),k3_xboole_0(X43,X45)) ),
    inference(variable_rename,[status(thm)],[t50_xboole_1])).

fof(c_0_22,plain,(
    ! [X40,X41,X42] : k3_xboole_0(X40,k4_xboole_0(X41,X42)) = k4_xboole_0(k3_xboole_0(X40,X41),X42) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X54] : k5_xboole_0(X54,k1_xboole_0) = X54 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_27,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_24]),c_0_24])).

fof(c_0_32,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_33,plain,(
    ! [X22] : k3_xboole_0(X22,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_34,plain,(
    ! [X63,X64,X65] : k4_xboole_0(k5_xboole_0(X63,X64),X65) = k2_xboole_0(k4_xboole_0(X63,k2_xboole_0(X64,X65)),k4_xboole_0(X64,k2_xboole_0(X63,X65))) ),
    inference(variable_rename,[status(thm)],[t99_xboole_1])).

fof(c_0_35,plain,(
    ! [X61,X62] : k2_xboole_0(X61,X62) = k5_xboole_0(X61,k4_xboole_0(X62,X61)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_36,plain,(
    ! [X19,X20,X21] : k3_xboole_0(X19,k2_xboole_0(X20,X21)) = k2_xboole_0(k3_xboole_0(X19,X20),k3_xboole_0(X19,X21)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

fof(c_0_37,plain,(
    ! [X55,X56,X57] : k5_xboole_0(k5_xboole_0(X55,X56),X57) = k5_xboole_0(X55,k5_xboole_0(X56,X57)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_38,plain,(
    ! [X58] : k5_xboole_0(X58,X58) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_24]),c_0_24])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_24]),c_0_24])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_30])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X1,X3)))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_45]),c_0_39])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1))))),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1))))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47]),c_0_47]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) = k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X3),k3_xboole_0(k3_xboole_0(X1,X3),k3_xboole_0(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_47]),c_0_47]),c_0_24]),c_0_24])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_45])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1)))),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1))))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_49]),c_0_49]),c_0_49])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_40])).

cnf(c_0_61,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) = k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_42]),c_0_52])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_30]),c_0_31])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_57,c_0_40])).

fof(c_0_64,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X11,X10)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_44])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1)))),k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1))))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_49]),c_0_40])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_54]),c_0_45]),c_0_39])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_69,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_44])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_42])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,X2)))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_50]),c_0_39]),c_0_68]),c_0_50]),c_0_50]),c_0_39]),c_0_69]),c_0_39]),c_0_57]),c_0_44])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_47]),c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_74,plain,
    ( k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X3,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_65]),c_0_39])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X1))) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_72]),c_0_57])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2))))))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_49]),c_0_49])).

cnf(c_0_77,plain,
    ( k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X2,X3)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_44])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_57]),c_0_44]),c_0_49]),c_0_75])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2))))))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_60]),c_0_49]),c_0_40])).

cnf(c_0_80,plain,
    ( k3_xboole_0(k3_xboole_0(X1,k5_xboole_0(X1,X2)),k3_xboole_0(X2,X3)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X2)))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_78]),c_0_78]),c_0_80]),c_0_39])).

cnf(c_0_82,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_44]),c_0_42])).

cnf(c_0_83,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_75])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_81]),c_0_57])).

cnf(c_0_85,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3))) = k3_xboole_0(X2,k3_xboole_0(X1,k5_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_78]),c_0_78])).

cnf(c_0_86,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,k5_xboole_0(X1,X2))) = X2 ),
    inference(spm,[status(thm)],[c_0_63,c_0_83])).

cnf(c_0_87,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_84]),c_0_50])).

cnf(c_0_88,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,X3)))) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_57])).

cnf(c_0_89,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_45]),c_0_39])).

fof(c_0_90,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(X1,k5_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(assume_negation,[status(cth)],[t102_xboole_1])).

cnf(c_0_91,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_88])).

cnf(c_0_92,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X3,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_87]),c_0_39]),c_0_67]),c_0_89])).

fof(c_0_93,negated_conjecture,(
    k4_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)) != k2_xboole_0(k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_90])])])).

fof(c_0_94,plain,(
    ! [X34,X35] : k4_xboole_0(X34,k2_xboole_0(X34,X35)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_95,plain,(
    ! [X28,X29,X30] : k4_xboole_0(k4_xboole_0(X28,X29),X30) = k4_xboole_0(X28,k2_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_96,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X1,X2),X3)) = k3_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_91,c_0_44])).

cnf(c_0_97,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X2),X3)) = k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_78]),c_0_78])).

cnf(c_0_98,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X1),X3)) = k3_xboole_0(k3_xboole_0(X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( k4_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)) != k2_xboole_0(k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_100,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_101,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_102,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_96]),c_0_97]),c_0_88])).

cnf(c_0_103,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_98]),c_0_97]),c_0_57])).

cnf(c_0_104,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))) != k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0))))),k5_xboole_0(k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0),k3_xboole_0(k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0),k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0)))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_47]),c_0_47]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_105,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_47]),c_0_24]),c_0_24])).

cnf(c_0_106,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_47]),c_0_24]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_107,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X3,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_102]),c_0_103])).

cnf(c_0_108,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_63]),c_0_49])).

cnf(c_0_109,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)))),k5_xboole_0(k3_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_49])).

cnf(c_0_110,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_105]),c_0_39])).

cnf(c_0_111,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))) ),
    inference(rw,[status(thm)],[c_0_106,c_0_49])).

cnf(c_0_112,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_107])).

cnf(c_0_113,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X1,k5_xboole_0(X2,X3))))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_49])).

cnf(c_0_114,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),X3) = k5_xboole_0(X3,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_87]),c_0_39])).

cnf(c_0_115,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_75]),c_0_44])).

cnf(c_0_116,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)))),k3_xboole_0(esk3_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))))))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_42]),c_0_42])).

cnf(c_0_117,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) = X1 ),
    inference(spm,[status(thm)],[c_0_110,c_0_44])).

cnf(c_0_118,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),X3),X4)) = k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))),X4) ),
    inference(spm,[status(thm)],[c_0_49,c_0_42])).

cnf(c_0_119,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,k5_xboole_0(X1,X2)),X3))) = k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X3,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_78]),c_0_78]),c_0_78])).

cnf(c_0_120,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X3,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_92,c_0_112])).

cnf(c_0_121,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(k5_xboole_0(X3,X2),X1)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_60]),c_0_114])).

cnf(c_0_122,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_57]),c_0_44])).

cnf(c_0_123,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_82]),c_0_117]),c_0_50]),c_0_45]),c_0_39]),c_0_40])).

cnf(c_0_124,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),X3),X4)) = k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3))),X4) ),
    inference(rw,[status(thm)],[c_0_118,c_0_78])).

cnf(c_0_125,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_40]),c_0_49])).

cnf(c_0_126,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X3,k5_xboole_0(X1,X2))))) = k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X3,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_112]),c_0_120])).

cnf(c_0_127,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X3,k5_xboole_0(X3,k5_xboole_0(X2,X1)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_39]),c_0_112]),c_0_107])).

cnf(c_0_128,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_123,c_0_83])).

cnf(c_0_129,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X1))) = k5_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_63,c_0_49])).

cnf(c_0_130,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X2,k3_xboole_0(X1,X3)),X4)) = k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3))),X4) ),
    inference(rw,[status(thm)],[c_0_124,c_0_112])).

cnf(c_0_131,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X3,k5_xboole_0(X3,X2)))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X3,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_78]),c_0_78])).

cnf(c_0_132,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X2,X1))) = X3 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_87]),c_0_39])).

cnf(c_0_133,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X2,X1)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_39]),c_0_49]),c_0_49]),c_0_57]),c_0_50]),c_0_45]),c_0_49]),c_0_39]),c_0_49]),c_0_57]),c_0_50]),c_0_45])).

cnf(c_0_134,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)))))) != k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_128,c_0_78])).

cnf(c_0_135,plain,
    ( k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k5_xboole_0(X4,k3_xboole_0(X2,k3_xboole_0(X1,k5_xboole_0(X1,X3))))) = k5_xboole_0(X4,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_49]),c_0_129])).

cnf(c_0_136,plain,
    ( k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,X3)),k3_xboole_0(X1,k3_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(X4,X2))))) = k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(X4,X2)))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_60]),c_0_49])).

cnf(c_0_137,plain,
    ( k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X3))),k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X1,k5_xboole_0(X1,X3))))) = k3_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_131]),c_0_112]),c_0_120])).

cnf(c_0_138,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X2,X1)) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_133]),c_0_39])).

cnf(c_0_139,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk3_0)),k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)))))) != k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_134,c_0_107])).

cnf(c_0_140,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X3,X2),X1)) = k3_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_57]),c_0_78]),c_0_137]),c_0_114])).

cnf(c_0_141,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X2,X1),X3)) = k3_xboole_0(k5_xboole_0(X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_112,c_0_138])).

cnf(c_0_142,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)))))) != k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_120]),c_0_44])).

cnf(c_0_143,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) = k3_xboole_0(k5_xboole_0(X3,X2),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_140])).

cnf(c_0_144,plain,
    ( k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,X1)),X3) = k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X1),X3)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_83])).

cnf(c_0_145,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),X3) = k3_xboole_0(X3,k5_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_141]),c_0_138])).

cnf(c_0_146,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_142,c_0_143]),c_0_49]),c_0_144]),c_0_143]),c_0_50]),c_0_69]),c_0_39]),c_0_145]),c_0_40]),c_0_78])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:42:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 33.83/34.06  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 33.83/34.06  # and selection function SelectComplexExceptUniqMaxHorn.
% 33.83/34.06  #
% 33.83/34.06  # Preprocessing time       : 0.027 s
% 33.83/34.06  # Presaturation interreduction done
% 33.83/34.06  
% 33.83/34.06  # Proof found!
% 33.83/34.06  # SZS status Theorem
% 33.83/34.06  # SZS output start CNFRefutation
% 33.83/34.06  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 33.83/34.06  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 33.83/34.06  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 33.83/34.06  fof(t50_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 33.83/34.06  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 33.83/34.06  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 33.83/34.06  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 33.83/34.06  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 33.83/34.06  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 33.83/34.06  fof(t99_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k5_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_xboole_1)).
% 33.83/34.06  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 33.83/34.06  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 33.83/34.06  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 33.83/34.06  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 33.83/34.06  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 33.83/34.06  fof(t102_xboole_1, conjecture, ![X1, X2, X3]:k4_xboole_0(X1,k5_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(k3_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_xboole_1)).
% 33.83/34.06  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 33.83/34.06  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 33.83/34.06  fof(c_0_18, plain, ![X38, X39]:k4_xboole_0(X38,k4_xboole_0(X38,X39))=k3_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 33.83/34.06  fof(c_0_19, plain, ![X17, X18]:k4_xboole_0(X17,X18)=k5_xboole_0(X17,k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 33.83/34.06  fof(c_0_20, plain, ![X36, X37]:k4_xboole_0(X36,k3_xboole_0(X36,X37))=k4_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 33.83/34.06  fof(c_0_21, plain, ![X43, X44, X45]:k3_xboole_0(X43,k4_xboole_0(X44,X45))=k4_xboole_0(k3_xboole_0(X43,X44),k3_xboole_0(X43,X45)), inference(variable_rename,[status(thm)],[t50_xboole_1])).
% 33.83/34.06  fof(c_0_22, plain, ![X40, X41, X42]:k3_xboole_0(X40,k4_xboole_0(X41,X42))=k4_xboole_0(k3_xboole_0(X40,X41),X42), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 33.83/34.06  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 33.83/34.06  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 33.83/34.06  cnf(c_0_25, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 33.83/34.06  fof(c_0_26, plain, ![X54]:k5_xboole_0(X54,k1_xboole_0)=X54, inference(variable_rename,[status(thm)],[t5_boole])).
% 33.83/34.06  fof(c_0_27, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k5_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 33.83/34.06  cnf(c_0_28, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 33.83/34.06  cnf(c_0_29, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 33.83/34.06  cnf(c_0_30, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24])).
% 33.83/34.06  cnf(c_0_31, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_24]), c_0_24])).
% 33.83/34.06  fof(c_0_32, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 33.83/34.06  fof(c_0_33, plain, ![X22]:k3_xboole_0(X22,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 33.83/34.06  fof(c_0_34, plain, ![X63, X64, X65]:k4_xboole_0(k5_xboole_0(X63,X64),X65)=k2_xboole_0(k4_xboole_0(X63,k2_xboole_0(X64,X65)),k4_xboole_0(X64,k2_xboole_0(X63,X65))), inference(variable_rename,[status(thm)],[t99_xboole_1])).
% 33.83/34.06  fof(c_0_35, plain, ![X61, X62]:k2_xboole_0(X61,X62)=k5_xboole_0(X61,k4_xboole_0(X62,X61)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 33.83/34.06  fof(c_0_36, plain, ![X19, X20, X21]:k3_xboole_0(X19,k2_xboole_0(X20,X21))=k2_xboole_0(k3_xboole_0(X19,X20),k3_xboole_0(X19,X21)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 33.83/34.06  fof(c_0_37, plain, ![X55, X56, X57]:k5_xboole_0(k5_xboole_0(X55,X56),X57)=k5_xboole_0(X55,k5_xboole_0(X56,X57)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 33.83/34.06  fof(c_0_38, plain, ![X58]:k5_xboole_0(X58,X58)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 33.83/34.06  cnf(c_0_39, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 33.83/34.06  cnf(c_0_40, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 33.83/34.06  cnf(c_0_41, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_24]), c_0_24])).
% 33.83/34.06  cnf(c_0_42, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_24]), c_0_24])).
% 33.83/34.06  cnf(c_0_43, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_30])).
% 33.83/34.06  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 33.83/34.06  cnf(c_0_45, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 33.83/34.06  cnf(c_0_46, plain, (k4_xboole_0(k5_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 33.83/34.06  cnf(c_0_47, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 33.83/34.06  cnf(c_0_48, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 33.83/34.06  cnf(c_0_49, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 33.83/34.06  cnf(c_0_50, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 33.83/34.06  cnf(c_0_51, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 33.83/34.06  cnf(c_0_52, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X1,X3))))=k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 33.83/34.06  cnf(c_0_53, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 33.83/34.06  cnf(c_0_54, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_45]), c_0_39])).
% 33.83/34.06  cnf(c_0_55, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),X3))=k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1))))),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1))))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_47]), c_0_47]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 33.83/34.06  cnf(c_0_56, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))=k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X3),k3_xboole_0(k3_xboole_0(X1,X3),k3_xboole_0(X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_47]), c_0_47]), c_0_24]), c_0_24])).
% 33.83/34.06  cnf(c_0_57, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 33.83/34.06  cnf(c_0_58, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_45])).
% 33.83/34.06  cnf(c_0_59, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1)))),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1))))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_49]), c_0_49]), c_0_49])).
% 33.83/34.06  cnf(c_0_60, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_49, c_0_40])).
% 33.83/34.06  cnf(c_0_61, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))))=k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_42]), c_0_52])).
% 33.83/34.06  cnf(c_0_62, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_30]), c_0_31])).
% 33.83/34.06  cnf(c_0_63, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(spm,[status(thm)],[c_0_57, c_0_40])).
% 33.83/34.06  fof(c_0_64, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k2_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 33.83/34.06  cnf(c_0_65, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_44])).
% 33.83/34.06  cnf(c_0_66, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1)))),k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1))))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60]), c_0_49]), c_0_40])).
% 33.83/34.06  cnf(c_0_67, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_54]), c_0_45]), c_0_39])).
% 33.83/34.06  cnf(c_0_68, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 33.83/34.06  cnf(c_0_69, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_44])).
% 33.83/34.06  cnf(c_0_70, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 33.83/34.06  cnf(c_0_71, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_42])).
% 33.83/34.06  cnf(c_0_72, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,X2))))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_50]), c_0_39]), c_0_68]), c_0_50]), c_0_50]), c_0_39]), c_0_69]), c_0_39]), c_0_57]), c_0_44])).
% 33.83/34.06  cnf(c_0_73, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_47]), c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 33.83/34.06  cnf(c_0_74, plain, (k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X3,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_65]), c_0_39])).
% 33.83/34.06  cnf(c_0_75, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X1)))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_72]), c_0_57])).
% 33.83/34.06  cnf(c_0_76, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2)))))))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_49]), c_0_49])).
% 33.83/34.06  cnf(c_0_77, plain, (k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X2,X3))=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_44])).
% 33.83/34.06  cnf(c_0_78, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_57]), c_0_44]), c_0_49]), c_0_75])).
% 33.83/34.06  cnf(c_0_79, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2)))))))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_60]), c_0_49]), c_0_40])).
% 33.83/34.06  cnf(c_0_80, plain, (k3_xboole_0(k3_xboole_0(X1,k5_xboole_0(X1,X2)),k3_xboole_0(X2,X3))=k1_xboole_0), inference(rw,[status(thm)],[c_0_77, c_0_78])).
% 33.83/34.06  cnf(c_0_81, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X2))))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_78]), c_0_78]), c_0_80]), c_0_39])).
% 33.83/34.06  cnf(c_0_82, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_44]), c_0_42])).
% 33.83/34.06  cnf(c_0_83, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,k5_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_57, c_0_75])).
% 33.83/34.06  cnf(c_0_84, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_81]), c_0_57])).
% 33.83/34.06  cnf(c_0_85, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3)))=k3_xboole_0(X2,k3_xboole_0(X1,k5_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_78]), c_0_78])).
% 33.83/34.06  cnf(c_0_86, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,k5_xboole_0(X1,X2)))=X2), inference(spm,[status(thm)],[c_0_63, c_0_83])).
% 33.83/34.06  cnf(c_0_87, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_84]), c_0_50])).
% 33.83/34.06  cnf(c_0_88, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,X3))))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_85, c_0_57])).
% 33.83/34.06  cnf(c_0_89, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_45]), c_0_39])).
% 33.83/34.06  fof(c_0_90, negated_conjecture, ~(![X1, X2, X3]:k4_xboole_0(X1,k5_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(assume_negation,[status(cth)],[t102_xboole_1])).
% 33.83/34.06  cnf(c_0_91, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3)))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_43, c_0_88])).
% 33.83/34.06  cnf(c_0_92, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X3,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_87]), c_0_39]), c_0_67]), c_0_89])).
% 33.83/34.06  fof(c_0_93, negated_conjecture, k4_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))!=k2_xboole_0(k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_90])])])).
% 33.83/34.06  fof(c_0_94, plain, ![X34, X35]:k4_xboole_0(X34,k2_xboole_0(X34,X35))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 33.83/34.06  fof(c_0_95, plain, ![X28, X29, X30]:k4_xboole_0(k4_xboole_0(X28,X29),X30)=k4_xboole_0(X28,k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 33.83/34.06  cnf(c_0_96, plain, (k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X1,X2),X3))=k3_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_91, c_0_44])).
% 33.83/34.06  cnf(c_0_97, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X2),X3))=k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_78]), c_0_78])).
% 33.83/34.06  cnf(c_0_98, plain, (k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X1),X3))=k3_xboole_0(k3_xboole_0(X2,X1),X3)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 33.83/34.06  cnf(c_0_99, negated_conjecture, (k4_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))!=k2_xboole_0(k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 33.83/34.06  cnf(c_0_100, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_94])).
% 33.83/34.06  cnf(c_0_101, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_95])).
% 33.83/34.06  cnf(c_0_102, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_96]), c_0_97]), c_0_88])).
% 33.83/34.06  cnf(c_0_103, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_98]), c_0_97]), c_0_57])).
% 33.83/34.06  cnf(c_0_104, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)))!=k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0))))),k5_xboole_0(k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0),k3_xboole_0(k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0),k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_47]), c_0_47]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 33.83/34.06  cnf(c_0_105, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_47]), c_0_24]), c_0_24])).
% 33.83/34.06  cnf(c_0_106, plain, (k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3))=k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_47]), c_0_24]), c_0_24]), c_0_24]), c_0_24])).
% 33.83/34.06  cnf(c_0_107, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X3,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_102]), c_0_103])).
% 33.83/34.06  cnf(c_0_108, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3)))=k5_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_63]), c_0_49])).
% 33.83/34.06  cnf(c_0_109, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)))),k5_xboole_0(k3_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)))))))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_49])).
% 33.83/34.06  cnf(c_0_110, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_105]), c_0_39])).
% 33.83/34.06  cnf(c_0_111, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)))=k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))), inference(rw,[status(thm)],[c_0_106, c_0_49])).
% 33.83/34.06  cnf(c_0_112, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_44, c_0_107])).
% 33.83/34.06  cnf(c_0_113, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X1,k5_xboole_0(X2,X3)))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_49])).
% 33.83/34.06  cnf(c_0_114, plain, (k5_xboole_0(k3_xboole_0(X1,X2),X3)=k5_xboole_0(X3,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_87]), c_0_39])).
% 33.83/34.06  cnf(c_0_115, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_75]), c_0_44])).
% 33.83/34.06  cnf(c_0_116, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)))),k3_xboole_0(esk3_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)))))))))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_42]), c_0_42])).
% 33.83/34.06  cnf(c_0_117, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))=X1), inference(spm,[status(thm)],[c_0_110, c_0_44])).
% 33.83/34.06  cnf(c_0_118, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),X3),X4))=k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))),X4)), inference(spm,[status(thm)],[c_0_49, c_0_42])).
% 33.83/34.06  cnf(c_0_119, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,k5_xboole_0(X1,X2)),X3)))=k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X3,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_78]), c_0_78]), c_0_78])).
% 33.83/34.06  cnf(c_0_120, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X3,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_92, c_0_112])).
% 33.83/34.06  cnf(c_0_121, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(k5_xboole_0(X3,X2),X1))))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_60]), c_0_114])).
% 33.83/34.06  cnf(c_0_122, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_57]), c_0_44])).
% 33.83/34.06  cnf(c_0_123, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_82]), c_0_117]), c_0_50]), c_0_45]), c_0_39]), c_0_40])).
% 33.83/34.06  cnf(c_0_124, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),X3),X4))=k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3))),X4)), inference(rw,[status(thm)],[c_0_118, c_0_78])).
% 33.83/34.06  cnf(c_0_125, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_40]), c_0_49])).
% 33.83/34.06  cnf(c_0_126, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X3,k5_xboole_0(X1,X2)))))=k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X3,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_112]), c_0_120])).
% 33.83/34.06  cnf(c_0_127, plain, (k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X3,k5_xboole_0(X3,k5_xboole_0(X2,X1))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_39]), c_0_112]), c_0_107])).
% 33.83/34.06  cnf(c_0_128, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_123, c_0_83])).
% 33.83/34.06  cnf(c_0_129, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X1)))=k5_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_63, c_0_49])).
% 33.83/34.06  cnf(c_0_130, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X2,k3_xboole_0(X1,X3)),X4))=k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X3))),X4)), inference(rw,[status(thm)],[c_0_124, c_0_112])).
% 33.83/34.06  cnf(c_0_131, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X3,k5_xboole_0(X3,X2))))=k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X3,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_78]), c_0_78])).
% 33.83/34.06  cnf(c_0_132, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X2,X1)))=X3), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_87]), c_0_39])).
% 33.83/34.06  cnf(c_0_133, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X2,X1))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_39]), c_0_49]), c_0_49]), c_0_57]), c_0_50]), c_0_45]), c_0_49]), c_0_39]), c_0_49]), c_0_57]), c_0_50]), c_0_45])).
% 33.83/34.06  cnf(c_0_134, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))))))!=k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_128, c_0_78])).
% 33.83/34.06  cnf(c_0_135, plain, (k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k5_xboole_0(X4,k3_xboole_0(X2,k3_xboole_0(X1,k5_xboole_0(X1,X3)))))=k5_xboole_0(X4,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_49]), c_0_129])).
% 33.83/34.06  cnf(c_0_136, plain, (k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,X3)),k3_xboole_0(X1,k3_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(X4,X2)))))=k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(X4,X2))))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_60]), c_0_49])).
% 33.83/34.06  cnf(c_0_137, plain, (k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X3))),k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X1,k5_xboole_0(X1,X3)))))=k3_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_131]), c_0_112]), c_0_120])).
% 33.83/34.06  cnf(c_0_138, plain, (k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X2,X1))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_133]), c_0_39])).
% 33.83/34.06  cnf(c_0_139, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk3_0)),k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))))))!=k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_134, c_0_107])).
% 33.83/34.06  cnf(c_0_140, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X3,X2),X1))=k3_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_136]), c_0_57]), c_0_78]), c_0_137]), c_0_114])).
% 33.83/34.06  cnf(c_0_141, plain, (k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X2,X1),X3))=k3_xboole_0(k5_xboole_0(X2,X1),X3)), inference(spm,[status(thm)],[c_0_112, c_0_138])).
% 33.83/34.06  cnf(c_0_142, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))))))!=k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139, c_0_120]), c_0_44])).
% 33.83/34.06  cnf(c_0_143, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))=k3_xboole_0(k5_xboole_0(X3,X2),X1)), inference(spm,[status(thm)],[c_0_57, c_0_140])).
% 33.83/34.06  cnf(c_0_144, plain, (k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,X1)),X3)=k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X1),X3))), inference(spm,[status(thm)],[c_0_49, c_0_83])).
% 33.83/34.06  cnf(c_0_145, plain, (k3_xboole_0(k5_xboole_0(X1,X2),X3)=k3_xboole_0(X3,k5_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_141]), c_0_138])).
% 33.83/34.06  cnf(c_0_146, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_142, c_0_143]), c_0_49]), c_0_144]), c_0_143]), c_0_50]), c_0_69]), c_0_39]), c_0_145]), c_0_40]), c_0_78])]), ['proof']).
% 33.83/34.06  # SZS output end CNFRefutation
% 33.83/34.06  # Proof object total steps             : 147
% 33.83/34.06  # Proof object clause steps            : 110
% 33.83/34.06  # Proof object formula steps           : 37
% 33.83/34.06  # Proof object conjectures             : 13
% 33.83/34.06  # Proof object clause conjectures      : 10
% 33.83/34.06  # Proof object formula conjectures     : 3
% 33.83/34.06  # Proof object initial clauses used    : 18
% 33.83/34.06  # Proof object initial formulas used   : 18
% 33.83/34.06  # Proof object generating inferences   : 57
% 33.83/34.06  # Proof object simplifying inferences  : 179
% 33.83/34.06  # Training examples: 0 positive, 0 negative
% 33.83/34.06  # Parsed axioms                        : 30
% 33.83/34.06  # Removed by relevancy pruning/SinE    : 0
% 33.83/34.06  # Initial clauses                      : 30
% 33.83/34.06  # Removed in clause preprocessing      : 2
% 33.83/34.06  # Initial clauses in saturation        : 28
% 33.83/34.06  # Processed clauses                    : 19996
% 33.83/34.06  # ...of these trivial                  : 4824
% 33.83/34.06  # ...subsumed                          : 13900
% 33.83/34.06  # ...remaining for further processing  : 1272
% 33.83/34.06  # Other redundant clauses eliminated   : 0
% 33.83/34.06  # Clauses deleted for lack of memory   : 170378
% 33.83/34.06  # Backward-subsumed                    : 2
% 33.83/34.06  # Backward-rewritten                   : 364
% 33.83/34.06  # Generated clauses                    : 1654311
% 33.83/34.06  # ...of the previous two non-trivial   : 1340659
% 33.83/34.06  # Contextual simplify-reflections      : 0
% 33.83/34.06  # Paramodulations                      : 1654311
% 33.83/34.06  # Factorizations                       : 0
% 33.83/34.06  # Equation resolutions                 : 0
% 33.83/34.06  # Propositional unsat checks           : 0
% 33.83/34.06  #    Propositional check models        : 0
% 33.83/34.06  #    Propositional check unsatisfiable : 0
% 33.83/34.06  #    Propositional clauses             : 0
% 33.83/34.06  #    Propositional clauses after purity: 0
% 33.83/34.06  #    Propositional unsat core size     : 0
% 33.83/34.06  #    Propositional preprocessing time  : 0.000
% 33.83/34.06  #    Propositional encoding time       : 0.000
% 33.83/34.06  #    Propositional solver time         : 0.000
% 33.83/34.06  #    Success case prop preproc time    : 0.000
% 33.83/34.06  #    Success case prop encoding time   : 0.000
% 33.83/34.06  #    Success case prop solver time     : 0.000
% 33.83/34.06  # Current number of processed clauses  : 880
% 33.83/34.06  #    Positive orientable unit clauses  : 781
% 33.83/34.06  #    Positive unorientable unit clauses: 99
% 33.83/34.06  #    Negative unit clauses             : 0
% 33.83/34.06  #    Non-unit-clauses                  : 0
% 33.83/34.06  # Current number of unprocessed clauses: 682531
% 33.83/34.06  # ...number of literals in the above   : 682531
% 33.83/34.06  # Current number of archived formulas  : 0
% 33.83/34.06  # Current number of archived clauses   : 394
% 33.83/34.06  # Clause-clause subsumption calls (NU) : 0
% 33.83/34.06  # Rec. Clause-clause subsumption calls : 0
% 33.83/34.06  # Non-unit clause-clause subsumptions  : 0
% 33.83/34.06  # Unit Clause-clause subsumption calls : 9589
% 33.83/34.06  # Rewrite failures with RHS unbound    : 0
% 33.83/34.06  # BW rewrite match attempts            : 102148
% 33.83/34.06  # BW rewrite match successes           : 8810
% 33.83/34.06  # Condensation attempts                : 0
% 33.83/34.06  # Condensation successes               : 0
% 33.83/34.06  # Termbank termtop insertions          : 36429608
% 33.94/34.15  
% 33.94/34.15  # -------------------------------------------------
% 33.94/34.15  # User time                : 32.703 s
% 33.94/34.15  # System time              : 1.108 s
% 33.94/34.15  # Total time               : 33.811 s
% 33.94/34.15  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
