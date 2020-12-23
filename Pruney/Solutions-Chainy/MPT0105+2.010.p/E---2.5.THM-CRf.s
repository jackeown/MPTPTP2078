%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:09 EST 2020

% Result     : Theorem 37.48s
% Output     : CNFRefutation 37.48s
% Verified   : 
% Statistics : Number of formulae       :  120 (269369 expanded)
%              Number of clauses        :   97 (114734 expanded)
%              Number of leaves         :   11 (77317 expanded)
%              Depth                    :   29
%              Number of atoms          :  125 (287144 expanded)
%              Number of equality atoms :   90 (258992 expanded)
%              Maximal formula depth    :    6 (   1 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l98_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t98_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(c_0_11,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k4_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[l98_xboole_1])).

fof(c_0_12,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X23,X24] : k2_xboole_0(X23,X24) = k5_xboole_0(k5_xboole_0(X23,X24),k3_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_14,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X18,X19] :
      ( ( ~ r1_xboole_0(X18,X19)
        | k4_xboole_0(X18,X19) = X18 )
      & ( k4_xboole_0(X18,X19) != X18
        | r1_xboole_0(X18,X19) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_21,plain,(
    ! [X16,X17] : r1_xboole_0(k4_xboole_0(X16,X17),X17) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_15]),c_0_18]),c_0_18])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_15]),c_0_15])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X13] : k4_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_28,plain,(
    ! [X10] : k2_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X20,X21,X22] : k5_xboole_0(k5_xboole_0(X20,X21),X22) = k5_xboole_0(X20,k5_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_32,plain,
    ( r1_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_27])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_30])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,k4_xboole_0(X1,X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_30]),c_0_33]),c_0_33])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_34]),c_0_35])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3))) = k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_18]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,plain,
    ( r1_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_39])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))))) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_40])).

cnf(c_0_43,plain,
    ( r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_30]),c_0_30]),c_0_30]),c_0_33]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_33]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_33]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_29])).

cnf(c_0_45,plain,
    ( r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_35])).

fof(c_0_47,plain,(
    ! [X11,X12] : k2_xboole_0(X11,k4_xboole_0(X12,X11)) = k2_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_48,plain,
    ( r1_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_44]),c_0_35])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) = k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X2))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_30]),c_0_33]),c_0_33]),c_0_30]),c_0_33]),c_0_30]),c_0_35])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1))))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_45])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_44])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( r1_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_23])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_44])).

cnf(c_0_55,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))),k4_xboole_0(X3,X2)),k4_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))))) = k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X3,X2)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X3,X2)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_34]),c_0_23]),c_0_35]),c_0_35])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_35]),c_0_50])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_30]),c_0_33]),c_0_33]),c_0_33]),c_0_38])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_51]),c_0_52]),c_0_33]),c_0_52]),c_0_33])).

cnf(c_0_59,plain,
    ( r1_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))))))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1))))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_54]),c_0_57]),c_0_57])).

cnf(c_0_61,plain,
    ( r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_56])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)))))) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_58])).

cnf(c_0_63,plain,
    ( r1_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,plain,
    ( r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_35])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),X2),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),X2))) = k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(k1_xboole_0,X2),k4_xboole_0(X2,X2))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(k1_xboole_0,X2),k4_xboole_0(X2,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_35]),c_0_33]),c_0_30]),c_0_33]),c_0_30]),c_0_33]),c_0_30])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))))) = k4_xboole_0(X1,k4_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_62]),c_0_33]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_33]),c_0_33]),c_0_30]),c_0_33]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_35]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_33]),c_0_30]),c_0_33]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_33]),c_0_30]),c_0_30])).

cnf(c_0_67,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_35])).

cnf(c_0_68,plain,
    ( r1_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_44]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_69,plain,
    ( r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_50])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3))) = k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2)))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2)))))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_23])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_66]),c_0_35]),c_0_67]),c_0_46]),c_0_46]),c_0_35]),c_0_35])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_44]),c_0_35])).

cnf(c_0_73,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1)) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_68]),c_0_60])).

cnf(c_0_74,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1))))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_69])).

cnf(c_0_75,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) = k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_30]),c_0_33]),c_0_35]),c_0_33]),c_0_33])).

cnf(c_0_76,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k2_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_23])).

cnf(c_0_77,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_71]),c_0_71]),c_0_29]),c_0_46]),c_0_46]),c_0_46]),c_0_35]),c_0_71])).

cnf(c_0_78,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) = k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_23])).

cnf(c_0_79,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k2_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_35]),c_0_73]),c_0_74])).

cnf(c_0_80,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_35])).

cnf(c_0_81,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_35]),c_0_50])).

cnf(c_0_82,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_30]),c_0_52]),c_0_33]),c_0_30])).

cnf(c_0_83,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),X2),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X1))))) = k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(k1_xboole_0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_33]),c_0_30]),c_0_33]),c_0_30])).

cnf(c_0_84,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)) = k2_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_80]),c_0_75]),c_0_81])).

cnf(c_0_85,plain,
    ( r1_xboole_0(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_57])).

cnf(c_0_86,plain,
    ( r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_82]),c_0_46]),c_0_35]),c_0_77]),c_0_51]),c_0_46]),c_0_35]),c_0_77]),c_0_77]),c_0_77]),c_0_77])).

cnf(c_0_87,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_38]),c_0_57])).

cnf(c_0_88,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X1)))) = k2_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_84]),c_0_84]),c_0_84])).

cnf(c_0_89,plain,
    ( r1_xboole_0(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_35])).

cnf(c_0_90,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = k2_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_35])).

cnf(c_0_91,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))),X3),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))),X3))) = k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,X1),X3),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X2,X1),X3)))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,X1),X3),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X2,X1),X3)))))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_52])).

cnf(c_0_92,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_86])).

cnf(c_0_93,plain,
    ( r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_35])).

cnf(c_0_94,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_87]),c_0_88]),c_0_88]),c_0_87])).

cnf(c_0_95,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_96,plain,
    ( r1_xboole_0(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_66]),c_0_90])).

cnf(c_0_97,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))))) = k4_xboole_0(X1,k4_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_33]),c_0_51]),c_0_35]),c_0_77]),c_0_66]),c_0_90]),c_0_33]),c_0_51]),c_0_35]),c_0_77]),c_0_66]),c_0_33]),c_0_51]),c_0_35]),c_0_77]),c_0_66]),c_0_66]),c_0_35]),c_0_52]),c_0_33]),c_0_46]),c_0_35]),c_0_77]),c_0_92]),c_0_52]),c_0_33]),c_0_52]),c_0_33]),c_0_46]),c_0_35]),c_0_77]),c_0_92]),c_0_51]),c_0_35]),c_0_77]),c_0_66])).

cnf(c_0_98,plain,
    ( r1_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94]),c_0_94])).

cnf(c_0_99,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_35])).

fof(c_0_100,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(assume_negation,[status(cth)],[t98_xboole_1])).

cnf(c_0_101,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_96]),c_0_97])).

cnf(c_0_102,plain,
    ( r1_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_44]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_103,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(X1,X1)) = k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_99])).

fof(c_0_104,negated_conjecture,(
    k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_100])])])).

cnf(c_0_105,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))) = k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_101,c_0_35])).

cnf(c_0_106,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_102])).

cnf(c_0_107,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_35])).

cnf(c_0_108,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_94]),c_0_94])).

cnf(c_0_109,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_110,plain,
    ( r1_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_29]),c_0_35]),c_0_72])).

cnf(c_0_111,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_94]),c_0_94]),c_0_94])).

cnf(c_0_112,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_106]),c_0_46]),c_0_107]),c_0_44]),c_0_108])).

cnf(c_0_113,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k4_xboole_0(k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_109,c_0_18])).

cnf(c_0_114,plain,
    ( r1_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_44]),c_0_52]),c_0_52]),c_0_111]),c_0_54]),c_0_112]),c_0_112]),c_0_108])).

cnf(c_0_115,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)))) != k2_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_113,c_0_52])).

cnf(c_0_116,plain,
    ( r1_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_114,c_0_44])).

cnf(c_0_117,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk2_0,esk1_0))) != k2_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_115,c_0_44])).

cnf(c_0_118,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X2,X1))) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_116])).

cnf(c_0_119,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_118])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:59:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 37.48/37.65  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 37.48/37.65  # and selection function SelectNewComplexAHP.
% 37.48/37.65  #
% 37.48/37.65  # Preprocessing time       : 0.042 s
% 37.48/37.65  # Presaturation interreduction done
% 37.48/37.65  
% 37.48/37.65  # Proof found!
% 37.48/37.65  # SZS status Theorem
% 37.48/37.65  # SZS output start CNFRefutation
% 37.48/37.65  fof(l98_xboole_1, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 37.48/37.65  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 37.48/37.65  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 37.48/37.65  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 37.48/37.65  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 37.48/37.65  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 37.48/37.65  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 37.48/37.65  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 37.48/37.65  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 37.48/37.65  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 37.48/37.65  fof(t98_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 37.48/37.65  fof(c_0_11, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k4_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[l98_xboole_1])).
% 37.48/37.65  fof(c_0_12, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 37.48/37.65  fof(c_0_13, plain, ![X23, X24]:k2_xboole_0(X23,X24)=k5_xboole_0(k5_xboole_0(X23,X24),k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 37.48/37.65  cnf(c_0_14, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 37.48/37.65  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 37.48/37.65  fof(c_0_16, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 37.48/37.65  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 37.48/37.65  cnf(c_0_18, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 37.48/37.65  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 37.48/37.65  fof(c_0_20, plain, ![X18, X19]:((~r1_xboole_0(X18,X19)|k4_xboole_0(X18,X19)=X18)&(k4_xboole_0(X18,X19)!=X18|r1_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 37.48/37.65  fof(c_0_21, plain, ![X16, X17]:r1_xboole_0(k4_xboole_0(X16,X17),X17), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 37.48/37.65  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_15]), c_0_18]), c_0_18])).
% 37.48/37.65  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_15]), c_0_15])).
% 37.48/37.65  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 37.48/37.65  cnf(c_0_25, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 37.48/37.65  fof(c_0_26, plain, ![X13]:k4_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t3_boole])).
% 37.48/37.65  cnf(c_0_27, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 37.48/37.65  fof(c_0_28, plain, ![X10]:k2_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t1_boole])).
% 37.48/37.65  cnf(c_0_29, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 37.48/37.65  cnf(c_0_30, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 37.48/37.65  fof(c_0_31, plain, ![X20, X21, X22]:k5_xboole_0(k5_xboole_0(X20,X21),X22)=k5_xboole_0(X20,k5_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 37.48/37.65  cnf(c_0_32, plain, (r1_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))))), inference(spm,[status(thm)],[c_0_25, c_0_27])).
% 37.48/37.65  cnf(c_0_33, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 37.48/37.65  cnf(c_0_34, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_29, c_0_23])).
% 37.48/37.65  cnf(c_0_35, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_23, c_0_30])).
% 37.48/37.65  cnf(c_0_36, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 37.48/37.65  cnf(c_0_37, plain, (r1_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,k4_xboole_0(X1,X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_30]), c_0_33]), c_0_33])).
% 37.48/37.65  cnf(c_0_38, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))))=k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_34]), c_0_35])).
% 37.48/37.65  cnf(c_0_39, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3)))=k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_18]), c_0_18]), c_0_18]), c_0_18])).
% 37.48/37.65  cnf(c_0_40, plain, (r1_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))))), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 37.48/37.65  cnf(c_0_41, plain, (r1_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))))))), inference(spm,[status(thm)],[c_0_25, c_0_39])).
% 37.48/37.65  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))))=X1), inference(spm,[status(thm)],[c_0_24, c_0_40])).
% 37.48/37.65  cnf(c_0_43, plain, (r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_30]), c_0_30]), c_0_30]), c_0_33]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_33]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_33]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 37.48/37.65  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))=k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_23, c_0_29])).
% 37.48/37.65  cnf(c_0_45, plain, (r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 37.48/37.65  cnf(c_0_46, plain, (k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X1))=k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_35, c_0_35])).
% 37.48/37.65  fof(c_0_47, plain, ![X11, X12]:k2_xboole_0(X11,k4_xboole_0(X12,X11))=k2_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 37.48/37.65  cnf(c_0_48, plain, (r1_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_44]), c_0_35])).
% 37.48/37.65  cnf(c_0_49, plain, (k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))))=k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X2))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_30]), c_0_33]), c_0_33]), c_0_30]), c_0_33]), c_0_30]), c_0_35])).
% 37.48/37.65  cnf(c_0_50, plain, (k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)))))=k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_24, c_0_45])).
% 37.48/37.65  cnf(c_0_51, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)))=k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_46, c_0_44])).
% 37.48/37.65  cnf(c_0_52, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 37.48/37.65  cnf(c_0_53, plain, (r1_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))))))), inference(spm,[status(thm)],[c_0_48, c_0_23])).
% 37.48/37.65  cnf(c_0_54, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)))=k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_35, c_0_44])).
% 37.48/37.65  cnf(c_0_55, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))),k4_xboole_0(X3,X2)),k4_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))))))=k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X3,X2)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X3,X2)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X3))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_34]), c_0_23]), c_0_35]), c_0_35])).
% 37.48/37.65  cnf(c_0_56, plain, (k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))))=k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_35]), c_0_50])).
% 37.48/37.65  cnf(c_0_57, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_30]), c_0_33]), c_0_33]), c_0_33]), c_0_38])).
% 37.48/37.65  cnf(c_0_58, plain, (r1_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_51]), c_0_52]), c_0_33]), c_0_52]), c_0_33])).
% 37.48/37.65  cnf(c_0_59, plain, (r1_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)))))))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 37.48/37.65  cnf(c_0_60, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)))))=k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_54]), c_0_57]), c_0_57])).
% 37.48/37.65  cnf(c_0_61, plain, (r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))))), inference(spm,[status(thm)],[c_0_25, c_0_56])).
% 37.48/37.65  cnf(c_0_62, plain, (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))))))=X1), inference(spm,[status(thm)],[c_0_24, c_0_58])).
% 37.48/37.65  cnf(c_0_63, plain, (r1_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 37.48/37.65  cnf(c_0_64, plain, (r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))))), inference(spm,[status(thm)],[c_0_61, c_0_35])).
% 37.48/37.65  cnf(c_0_65, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),X2),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),X2)))=k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(k1_xboole_0,X2),k4_xboole_0(X2,X2))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(k1_xboole_0,X2),k4_xboole_0(X2,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_35]), c_0_33]), c_0_30]), c_0_33]), c_0_30]), c_0_33]), c_0_30])).
% 37.48/37.65  cnf(c_0_66, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))))=k4_xboole_0(X1,k4_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_62]), c_0_33]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_33]), c_0_33]), c_0_30]), c_0_33]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_35]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_33]), c_0_30]), c_0_33]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_33]), c_0_30]), c_0_30])).
% 37.48/37.65  cnf(c_0_67, plain, (k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),X1)=k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_29, c_0_35])).
% 37.48/37.65  cnf(c_0_68, plain, (r1_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_44]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 37.48/37.65  cnf(c_0_69, plain, (r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_50])).
% 37.48/37.65  cnf(c_0_70, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3)))=k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2)))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))))))), inference(spm,[status(thm)],[c_0_39, c_0_23])).
% 37.48/37.65  cnf(c_0_71, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))))))=k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_66]), c_0_35]), c_0_67]), c_0_46]), c_0_46]), c_0_35]), c_0_35])).
% 37.48/37.65  cnf(c_0_72, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_44]), c_0_35])).
% 37.48/37.65  cnf(c_0_73, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1))=k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_68]), c_0_60])).
% 37.48/37.65  cnf(c_0_74, plain, (k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)))))=k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_24, c_0_69])).
% 37.48/37.65  cnf(c_0_75, plain, (k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))))=k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_30]), c_0_33]), c_0_35]), c_0_33]), c_0_33])).
% 37.48/37.65  cnf(c_0_76, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k2_xboole_0(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_52, c_0_23])).
% 37.48/37.65  cnf(c_0_77, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))))=k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_71]), c_0_71]), c_0_29]), c_0_46]), c_0_46]), c_0_46]), c_0_35]), c_0_71])).
% 37.48/37.65  cnf(c_0_78, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))))=k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))))))), inference(spm,[status(thm)],[c_0_39, c_0_23])).
% 37.48/37.65  cnf(c_0_79, plain, (k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))=k2_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_35]), c_0_73]), c_0_74])).
% 37.48/37.65  cnf(c_0_80, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))=k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_73, c_0_35])).
% 37.48/37.65  cnf(c_0_81, plain, (k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))))=k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_35]), c_0_50])).
% 37.48/37.65  cnf(c_0_82, plain, (k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))))=k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_30]), c_0_52]), c_0_33]), c_0_30])).
% 37.48/37.65  cnf(c_0_83, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),X2),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X1)))))=k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(k1_xboole_0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_33]), c_0_30]), c_0_33]), c_0_30])).
% 37.48/37.65  cnf(c_0_84, plain, (k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1))=k2_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_80]), c_0_75]), c_0_81])).
% 37.48/37.65  cnf(c_0_85, plain, (r1_xboole_0(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_59, c_0_57])).
% 37.48/37.65  cnf(c_0_86, plain, (r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_82]), c_0_46]), c_0_35]), c_0_77]), c_0_51]), c_0_46]), c_0_35]), c_0_77]), c_0_77]), c_0_77]), c_0_77])).
% 37.48/37.65  cnf(c_0_87, plain, (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)))))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_38]), c_0_57])).
% 37.48/37.65  cnf(c_0_88, plain, (k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X1))))=k2_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_84]), c_0_84]), c_0_84])).
% 37.48/37.65  cnf(c_0_89, plain, (r1_xboole_0(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_85, c_0_35])).
% 37.48/37.65  cnf(c_0_90, plain, (k2_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))=k2_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_52, c_0_35])).
% 37.48/37.65  cnf(c_0_91, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))),X3),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))),X3)))=k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,X1),X3),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X2,X1),X3)))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,X1),X3),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X2,X1),X3))))))), inference(spm,[status(thm)],[c_0_39, c_0_52])).
% 37.48/37.65  cnf(c_0_92, plain, (k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))))=k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))), inference(spm,[status(thm)],[c_0_24, c_0_86])).
% 37.48/37.65  cnf(c_0_93, plain, (r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))))), inference(spm,[status(thm)],[c_0_86, c_0_35])).
% 37.48/37.65  cnf(c_0_94, plain, (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_87]), c_0_88]), c_0_88]), c_0_87])).
% 37.48/37.65  cnf(c_0_95, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 37.48/37.65  cnf(c_0_96, plain, (r1_xboole_0(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_66]), c_0_90])).
% 37.48/37.65  cnf(c_0_97, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X1))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))))=k4_xboole_0(X1,k4_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_33]), c_0_51]), c_0_35]), c_0_77]), c_0_66]), c_0_90]), c_0_33]), c_0_51]), c_0_35]), c_0_77]), c_0_66]), c_0_33]), c_0_51]), c_0_35]), c_0_77]), c_0_66]), c_0_66]), c_0_35]), c_0_52]), c_0_33]), c_0_46]), c_0_35]), c_0_77]), c_0_92]), c_0_52]), c_0_33]), c_0_52]), c_0_33]), c_0_46]), c_0_35]), c_0_77]), c_0_92]), c_0_51]), c_0_35]), c_0_77]), c_0_66])).
% 37.48/37.65  cnf(c_0_98, plain, (r1_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94]), c_0_94])).
% 37.48/37.65  cnf(c_0_99, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_95, c_0_35])).
% 37.48/37.65  fof(c_0_100, negated_conjecture, ~(![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(assume_negation,[status(cth)],[t98_xboole_1])).
% 37.48/37.65  cnf(c_0_101, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X1)))=k4_xboole_0(X1,k4_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_96]), c_0_97])).
% 37.48/37.65  cnf(c_0_102, plain, (r1_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_44]), c_0_30]), c_0_30]), c_0_30])).
% 37.48/37.65  cnf(c_0_103, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(X1,X1))=k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_24, c_0_99])).
% 37.48/37.65  fof(c_0_104, negated_conjecture, k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_100])])])).
% 37.48/37.65  cnf(c_0_105, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))),k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))=k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_101, c_0_35])).
% 37.48/37.65  cnf(c_0_106, plain, (k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_102])).
% 37.48/37.65  cnf(c_0_107, plain, (k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,X1))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_29, c_0_35])).
% 37.48/37.65  cnf(c_0_108, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_94]), c_0_94])).
% 37.48/37.65  cnf(c_0_109, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))), inference(split_conjunct,[status(thm)],[c_0_104])).
% 37.48/37.65  cnf(c_0_110, plain, (r1_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_29]), c_0_35]), c_0_72])).
% 37.48/37.65  cnf(c_0_111, plain, (k2_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_94]), c_0_94]), c_0_94])).
% 37.48/37.65  cnf(c_0_112, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_106]), c_0_46]), c_0_107]), c_0_44]), c_0_108])).
% 37.48/37.65  cnf(c_0_113, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k4_xboole_0(k2_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))))), inference(rw,[status(thm)],[c_0_109, c_0_18])).
% 37.48/37.65  cnf(c_0_114, plain, (r1_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_44]), c_0_52]), c_0_52]), c_0_111]), c_0_54]), c_0_112]), c_0_112]), c_0_108])).
% 37.48/37.65  cnf(c_0_115, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))))!=k2_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_113, c_0_52])).
% 37.48/37.65  cnf(c_0_116, plain, (r1_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_114, c_0_44])).
% 37.48/37.65  cnf(c_0_117, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk2_0,esk1_0)))!=k2_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_115, c_0_44])).
% 37.48/37.65  cnf(c_0_118, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X2,X1)))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_116])).
% 37.48/37.65  cnf(c_0_119, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_118])]), ['proof']).
% 37.48/37.65  # SZS output end CNFRefutation
% 37.48/37.65  # Proof object total steps             : 120
% 37.48/37.65  # Proof object clause steps            : 97
% 37.48/37.65  # Proof object formula steps           : 23
% 37.48/37.65  # Proof object conjectures             : 8
% 37.48/37.65  # Proof object clause conjectures      : 5
% 37.48/37.65  # Proof object formula conjectures     : 3
% 37.48/37.65  # Proof object initial clauses used    : 11
% 37.48/37.65  # Proof object initial formulas used   : 11
% 37.48/37.65  # Proof object generating inferences   : 70
% 37.48/37.65  # Proof object simplifying inferences  : 236
% 37.48/37.65  # Training examples: 0 positive, 0 negative
% 37.48/37.65  # Parsed axioms                        : 12
% 37.48/37.65  # Removed by relevancy pruning/SinE    : 0
% 37.48/37.65  # Initial clauses                      : 14
% 37.48/37.65  # Removed in clause preprocessing      : 2
% 37.48/37.65  # Initial clauses in saturation        : 12
% 37.48/37.65  # Processed clauses                    : 19262
% 37.48/37.65  # ...of these trivial                  : 9001
% 37.48/37.65  # ...subsumed                          : 8028
% 37.48/37.65  # ...remaining for further processing  : 2233
% 37.48/37.65  # Other redundant clauses eliminated   : 0
% 37.48/37.65  # Clauses deleted for lack of memory   : 0
% 37.48/37.65  # Backward-subsumed                    : 30
% 37.48/37.65  # Backward-rewritten                   : 1612
% 37.48/37.65  # Generated clauses                    : 1604952
% 37.48/37.65  # ...of the previous two non-trivial   : 1390082
% 37.48/37.65  # Contextual simplify-reflections      : 0
% 37.48/37.65  # Paramodulations                      : 1604940
% 37.48/37.65  # Factorizations                       : 0
% 37.48/37.65  # Equation resolutions                 : 12
% 37.48/37.65  # Propositional unsat checks           : 0
% 37.48/37.65  #    Propositional check models        : 0
% 37.48/37.65  #    Propositional check unsatisfiable : 0
% 37.48/37.65  #    Propositional clauses             : 0
% 37.48/37.65  #    Propositional clauses after purity: 0
% 37.48/37.65  #    Propositional unsat core size     : 0
% 37.48/37.65  #    Propositional preprocessing time  : 0.000
% 37.48/37.65  #    Propositional encoding time       : 0.000
% 37.48/37.65  #    Propositional solver time         : 0.000
% 37.48/37.65  #    Success case prop preproc time    : 0.000
% 37.48/37.65  #    Success case prop encoding time   : 0.000
% 37.48/37.65  #    Success case prop solver time     : 0.000
% 37.48/37.65  # Current number of processed clauses  : 579
% 37.48/37.65  #    Positive orientable unit clauses  : 423
% 37.48/37.65  #    Positive unorientable unit clauses: 36
% 37.48/37.65  #    Negative unit clauses             : 0
% 37.48/37.65  #    Non-unit-clauses                  : 120
% 37.48/37.65  # Current number of unprocessed clauses: 1366951
% 37.48/37.65  # ...number of literals in the above   : 1467826
% 37.48/37.65  # Current number of archived formulas  : 0
% 37.48/37.65  # Current number of archived clauses   : 1656
% 37.48/37.65  # Clause-clause subsumption calls (NU) : 130075
% 37.48/37.65  # Rec. Clause-clause subsumption calls : 130075
% 37.48/37.65  # Non-unit clause-clause subsumptions  : 4429
% 37.48/37.65  # Unit Clause-clause subsumption calls : 3448
% 37.48/37.65  # Rewrite failures with RHS unbound    : 0
% 37.48/37.65  # BW rewrite match attempts            : 82062
% 37.48/37.65  # BW rewrite match successes           : 345
% 37.48/37.65  # Condensation attempts                : 0
% 37.48/37.65  # Condensation successes               : 0
% 37.48/37.65  # Termbank termtop insertions          : 268439733
% 37.48/37.70  
% 37.48/37.70  # -------------------------------------------------
% 37.48/37.70  # User time                : 36.762 s
% 37.48/37.70  # System time              : 0.599 s
% 37.48/37.70  # Total time               : 37.361 s
% 37.48/37.70  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
