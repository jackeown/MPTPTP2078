%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:41 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 (40764 expanded)
%              Number of clauses        :   79 (18128 expanded)
%              Number of leaves         :   15 (11316 expanded)
%              Depth                    :   21
%              Number of atoms          :  157 (42423 expanded)
%              Number of equality atoms :   78 (39422 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :   12 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(c_0_15,plain,(
    ! [X12] : k3_xboole_0(X12,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_16,plain,(
    ! [X32,X33] : k3_xboole_0(X32,X33) = k5_xboole_0(k5_xboole_0(X32,X33),k2_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_17,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k3_xboole_0(X10,X11) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X20] : k5_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_21,plain,(
    ! [X29,X30,X31] : k5_xboole_0(k5_xboole_0(X29,X30),X31) = k5_xboole_0(X29,k5_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X13,X14] : r1_tarski(k4_xboole_0(X13,X14),X13) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_24,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_25,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_26,plain,(
    ! [X17,X18,X19] : k4_xboole_0(X17,k4_xboole_0(X18,X19)) = k2_xboole_0(k4_xboole_0(X17,X18),k3_xboole_0(X17,X19)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

fof(c_0_27,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_28,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_32,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_40,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_19])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))),k2_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))))) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_33]),c_0_33]),c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))))) = k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),k5_xboole_0(k5_xboole_0(X1,X3),k2_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_33]),c_0_33]),c_0_33]),c_0_19]),c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_19]),c_0_19])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,k1_xboole_0),X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_37])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_37])).

cnf(c_0_46,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),X1) ),
    inference(rw,[status(thm)],[c_0_40,c_0_30])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))))))))) = k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))))))))) = k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X3,k2_xboole_0(X1,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_30]),c_0_30])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X1,k1_xboole_0),k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_37]),c_0_29])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_38])).

cnf(c_0_52,plain,
    ( k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X1,X1)))),k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))) = k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k2_xboole_0(k1_xboole_0,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_37]),c_0_29])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k2_xboole_0(X1,k1_xboole_0),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

fof(c_0_55,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

fof(c_0_56,plain,(
    ! [X27,X28] :
      ( ( ~ r1_xboole_0(X27,X28)
        | k4_xboole_0(X27,X28) = X27 )
      & ( k4_xboole_0(X27,X28) != X27
        | r1_xboole_0(X27,X28) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_57,plain,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_53]),c_0_29]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_54]),c_0_29])).

fof(c_0_59,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))
    & ( ~ r1_tarski(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_55])])])).

fof(c_0_60,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_57]),c_0_29]),c_0_29]),c_0_29]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_37]),c_0_29]),c_0_38]),c_0_37]),c_0_29]),c_0_38]),c_0_37])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_33]),c_0_19])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_54,c_0_62])).

fof(c_0_67,plain,(
    ! [X25,X26] : r1_xboole_0(k4_xboole_0(X25,X26),X26) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_68,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,X22)
      | ~ r1_xboole_0(X22,X23)
      | r1_xboole_0(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(k5_xboole_0(esk2_0,esk3_0),k2_xboole_0(esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_33]),c_0_19])).

cnf(c_0_70,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_64,c_0_19])).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_65,c_0_30])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_66]),c_0_58])).

cnf(c_0_73,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_69,c_0_30])).

cnf(c_0_76,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_70,c_0_30])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X2,X1)) = X2
    | ~ r1_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_33]),c_0_19])).

cnf(c_0_79,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_80,negated_conjecture,
    ( r1_xboole_0(esk1_0,X1)
    | ~ r1_xboole_0(k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0)))),X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,plain,
    ( r1_tarski(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2) ),
    inference(rw,[status(thm)],[c_0_46,c_0_72])).

cnf(c_0_82,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_76,c_0_49])).

cnf(c_0_83,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_72,c_0_77])).

cnf(c_0_84,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),X2) ),
    inference(rw,[status(thm)],[c_0_78,c_0_30])).

cnf(c_0_85,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_79,c_0_19])).

cnf(c_0_86,negated_conjecture,
    ( r1_xboole_0(esk1_0,X1)
    | ~ r1_xboole_0(k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0)),X1) ),
    inference(rw,[status(thm)],[c_0_80,c_0_72])).

cnf(c_0_87,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_74,c_0_81])).

cnf(c_0_88,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_72]),c_0_66])])).

cnf(c_0_89,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X1) ),
    inference(rw,[status(thm)],[c_0_84,c_0_72])).

cnf(c_0_90,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_85,c_0_30])).

cnf(c_0_91,negated_conjecture,
    ( r1_xboole_0(esk1_0,X1)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_92,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_93,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( r1_xboole_0(esk1_0,k5_xboole_0(esk2_0,k2_xboole_0(X1,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_95,plain,
    ( r1_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_38]),c_0_37]),c_0_29])).

cnf(c_0_96,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = X3 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_72]),c_0_30])).

cnf(c_0_97,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0
    | ~ r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_93,c_0_81])).

cnf(c_0_98,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk2_0,k2_xboole_0(X1,esk2_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_94])).

cnf(c_0_99,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X3,k5_xboole_0(X1,k2_xboole_0(X2,X1))))) = k2_xboole_0(k5_xboole_0(X2,k2_xboole_0(X3,X2)),k5_xboole_0(X3,k5_xboole_0(X1,k2_xboole_0(X3,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_72]),c_0_72]),c_0_72]),c_0_72])).

cnf(c_0_100,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_72]),c_0_95])])).

cnf(c_0_101,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_49]),c_0_72]),c_0_72])).

cnf(c_0_102,negated_conjecture,
    ( k5_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_103,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1))))) = k2_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_66]),c_0_29]),c_0_101])).

cnf(c_0_104,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_102]),c_0_29])).

cnf(c_0_105,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0)
    | ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_106,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_84])).

cnf(c_0_107,negated_conjecture,
    ( k2_xboole_0(esk2_0,k5_xboole_0(esk1_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_66]),c_0_62]),c_0_66]),c_0_29]),c_0_101]),c_0_104])).

cnf(c_0_108,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106])])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_107]),c_0_30]),c_0_66]),c_0_29]),c_0_108]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:41:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.52  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.52  #
% 0.20/0.52  # Preprocessing time       : 0.027 s
% 0.20/0.52  # Presaturation interreduction done
% 0.20/0.52  
% 0.20/0.52  # Proof found!
% 0.20/0.52  # SZS status Theorem
% 0.20/0.52  # SZS output start CNFRefutation
% 0.20/0.52  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.52  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.20/0.52  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.52  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.20/0.52  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.20/0.52  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.52  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.52  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.52  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.20/0.52  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.52  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.20/0.52  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.52  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.52  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.52  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.20/0.52  fof(c_0_15, plain, ![X12]:k3_xboole_0(X12,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.52  fof(c_0_16, plain, ![X32, X33]:k3_xboole_0(X32,X33)=k5_xboole_0(k5_xboole_0(X32,X33),k2_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.20/0.52  fof(c_0_17, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k3_xboole_0(X10,X11)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.52  cnf(c_0_18, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.52  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.52  fof(c_0_20, plain, ![X20]:k5_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.20/0.52  fof(c_0_21, plain, ![X29, X30, X31]:k5_xboole_0(k5_xboole_0(X29,X30),X31)=k5_xboole_0(X29,k5_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.20/0.52  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.52  fof(c_0_23, plain, ![X13, X14]:r1_tarski(k4_xboole_0(X13,X14),X13), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.52  fof(c_0_24, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.52  fof(c_0_25, plain, ![X15, X16]:k4_xboole_0(X15,k4_xboole_0(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.52  fof(c_0_26, plain, ![X17, X18, X19]:k4_xboole_0(X17,k4_xboole_0(X18,X19))=k2_xboole_0(k4_xboole_0(X17,X18),k3_xboole_0(X17,X19)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.20/0.52  fof(c_0_27, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.52  cnf(c_0_28, plain, (k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.52  cnf(c_0_29, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.52  cnf(c_0_30, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.52  cnf(c_0_31, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_19])).
% 0.20/0.52  cnf(c_0_32, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.52  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.52  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.52  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.52  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.52  cnf(c_0_37, plain, (k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.52  cnf(c_0_38, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_30, c_0_29])).
% 0.20/0.52  cnf(c_0_39, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_30])).
% 0.20/0.52  cnf(c_0_40, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_19])).
% 0.20/0.52  cnf(c_0_41, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))),k2_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))))))=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_33]), c_0_33]), c_0_19]), c_0_19]), c_0_19])).
% 0.20/0.52  cnf(c_0_42, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))))))=k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),k5_xboole_0(k5_xboole_0(X1,X3),k2_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_33]), c_0_33]), c_0_33]), c_0_19]), c_0_19]), c_0_19]), c_0_19])).
% 0.20/0.52  cnf(c_0_43, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_19]), c_0_19])).
% 0.20/0.52  cnf(c_0_44, plain, (k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,k1_xboole_0),X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_30, c_0_37])).
% 0.20/0.52  cnf(c_0_45, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_37])).
% 0.20/0.52  cnf(c_0_46, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),X1)), inference(rw,[status(thm)],[c_0_40, c_0_30])).
% 0.20/0.52  cnf(c_0_47, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))))))))))=k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.20/0.52  cnf(c_0_48, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3)))))))))))=k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X3,k2_xboole_0(X1,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.20/0.52  cnf(c_0_49, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))=k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_30]), c_0_30])).
% 0.20/0.52  cnf(c_0_50, plain, (k5_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X1,k1_xboole_0),k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_37]), c_0_29])).
% 0.20/0.52  cnf(c_0_51, plain, (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_38])).
% 0.20/0.52  cnf(c_0_52, plain, (k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X1,X1)))),k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))=k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.52  cnf(c_0_53, plain, (k5_xboole_0(X1,k2_xboole_0(k1_xboole_0,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_37]), c_0_29])).
% 0.20/0.52  cnf(c_0_54, plain, (k5_xboole_0(k2_xboole_0(X1,k1_xboole_0),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.20/0.52  fof(c_0_55, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 0.20/0.52  fof(c_0_56, plain, ![X27, X28]:((~r1_xboole_0(X27,X28)|k4_xboole_0(X27,X28)=X27)&(k4_xboole_0(X27,X28)!=X27|r1_xboole_0(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.52  cnf(c_0_57, plain, (k2_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_53]), c_0_29]), c_0_29]), c_0_29]), c_0_29])).
% 0.20/0.52  cnf(c_0_58, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_54]), c_0_29])).
% 0.20/0.52  fof(c_0_59, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))&(~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_55])])])).
% 0.20/0.52  fof(c_0_60, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.52  cnf(c_0_61, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.52  cnf(c_0_62, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_57]), c_0_29]), c_0_29]), c_0_29]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_37]), c_0_29]), c_0_38]), c_0_37]), c_0_29]), c_0_38]), c_0_37])).
% 0.20/0.52  cnf(c_0_63, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.52  cnf(c_0_64, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.52  cnf(c_0_65, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_33]), c_0_19])).
% 0.20/0.52  cnf(c_0_66, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_54, c_0_62])).
% 0.20/0.52  fof(c_0_67, plain, ![X25, X26]:r1_xboole_0(k4_xboole_0(X25,X26),X26), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.52  fof(c_0_68, plain, ![X21, X22, X23]:(~r1_tarski(X21,X22)|~r1_xboole_0(X22,X23)|r1_xboole_0(X21,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.20/0.52  cnf(c_0_69, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(k5_xboole_0(esk2_0,esk3_0),k2_xboole_0(esk2_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_33]), c_0_19])).
% 0.20/0.52  cnf(c_0_70, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_64, c_0_19])).
% 0.20/0.52  cnf(c_0_71, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_65, c_0_30])).
% 0.20/0.52  cnf(c_0_72, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_66]), c_0_58])).
% 0.20/0.52  cnf(c_0_73, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.52  cnf(c_0_74, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.52  cnf(c_0_75, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0)))))), inference(rw,[status(thm)],[c_0_69, c_0_30])).
% 0.20/0.52  cnf(c_0_76, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_70, c_0_30])).
% 0.20/0.52  cnf(c_0_77, plain, (k5_xboole_0(X1,k2_xboole_0(X2,X1))=X2|~r1_xboole_0(X2,X1)), inference(rw,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.52  cnf(c_0_78, plain, (r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_33]), c_0_19])).
% 0.20/0.52  cnf(c_0_79, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.52  cnf(c_0_80, negated_conjecture, (r1_xboole_0(esk1_0,X1)|~r1_xboole_0(k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0)))),X1)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.52  cnf(c_0_81, plain, (r1_tarski(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2)), inference(rw,[status(thm)],[c_0_46, c_0_72])).
% 0.20/0.52  cnf(c_0_82, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_76, c_0_49])).
% 0.20/0.52  cnf(c_0_83, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_72, c_0_77])).
% 0.20/0.52  cnf(c_0_84, plain, (r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),X2)), inference(rw,[status(thm)],[c_0_78, c_0_30])).
% 0.20/0.52  cnf(c_0_85, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_79, c_0_19])).
% 0.20/0.52  cnf(c_0_86, negated_conjecture, (r1_xboole_0(esk1_0,X1)|~r1_xboole_0(k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0)),X1)), inference(rw,[status(thm)],[c_0_80, c_0_72])).
% 0.20/0.52  cnf(c_0_87, plain, (r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X3)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_74, c_0_81])).
% 0.20/0.52  cnf(c_0_88, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_72]), c_0_66])])).
% 0.20/0.52  cnf(c_0_89, plain, (r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X1)), inference(rw,[status(thm)],[c_0_84, c_0_72])).
% 0.20/0.52  cnf(c_0_90, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_85, c_0_30])).
% 0.20/0.52  cnf(c_0_91, negated_conjecture, (r1_xboole_0(esk1_0,X1)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.20/0.52  cnf(c_0_92, plain, (r1_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.20/0.52  cnf(c_0_93, plain, (k1_xboole_0=X1|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_90])).
% 0.20/0.52  cnf(c_0_94, negated_conjecture, (r1_xboole_0(esk1_0,k5_xboole_0(esk2_0,k2_xboole_0(X1,esk2_0)))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.20/0.52  cnf(c_0_95, plain, (r1_tarski(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_38]), c_0_37]), c_0_29])).
% 0.20/0.52  cnf(c_0_96, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,X3))))=X3), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_72]), c_0_30])).
% 0.20/0.52  cnf(c_0_97, plain, (k5_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0|~r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2)), inference(spm,[status(thm)],[c_0_93, c_0_81])).
% 0.20/0.52  cnf(c_0_98, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk2_0,k2_xboole_0(X1,esk2_0)),esk1_0)), inference(spm,[status(thm)],[c_0_88, c_0_94])).
% 0.20/0.52  cnf(c_0_99, plain, (k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X3,k5_xboole_0(X1,k2_xboole_0(X2,X1)))))=k2_xboole_0(k5_xboole_0(X2,k2_xboole_0(X3,X2)),k5_xboole_0(X3,k5_xboole_0(X1,k2_xboole_0(X3,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_72]), c_0_72]), c_0_72]), c_0_72])).
% 0.20/0.52  cnf(c_0_100, plain, (k2_xboole_0(X1,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_72]), c_0_95])])).
% 0.20/0.52  cnf(c_0_101, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_49]), c_0_72]), c_0_72])).
% 0.20/0.52  cnf(c_0_102, negated_conjecture, (k5_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.20/0.52  cnf(c_0_103, plain, (k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1)))))=k2_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_66]), c_0_29]), c_0_101])).
% 0.20/0.52  cnf(c_0_104, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_102]), c_0_29])).
% 0.20/0.52  cnf(c_0_105, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.52  cnf(c_0_106, negated_conjecture, (r1_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_80, c_0_84])).
% 0.20/0.52  cnf(c_0_107, negated_conjecture, (k2_xboole_0(esk2_0,k5_xboole_0(esk1_0,esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_66]), c_0_62]), c_0_66]), c_0_29]), c_0_101]), c_0_104])).
% 0.20/0.52  cnf(c_0_108, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_106])])).
% 0.20/0.52  cnf(c_0_109, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_107]), c_0_30]), c_0_66]), c_0_29]), c_0_108]), ['proof']).
% 0.20/0.52  # SZS output end CNFRefutation
% 0.20/0.52  # Proof object total steps             : 110
% 0.20/0.52  # Proof object clause steps            : 79
% 0.20/0.52  # Proof object formula steps           : 31
% 0.20/0.52  # Proof object conjectures             : 18
% 0.20/0.52  # Proof object clause conjectures      : 15
% 0.20/0.52  # Proof object formula conjectures     : 3
% 0.20/0.52  # Proof object initial clauses used    : 17
% 0.20/0.52  # Proof object initial formulas used   : 15
% 0.20/0.52  # Proof object generating inferences   : 32
% 0.20/0.52  # Proof object simplifying inferences  : 113
% 0.20/0.52  # Training examples: 0 positive, 0 negative
% 0.20/0.52  # Parsed axioms                        : 16
% 0.20/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.52  # Initial clauses                      : 19
% 0.20/0.52  # Removed in clause preprocessing      : 2
% 0.20/0.52  # Initial clauses in saturation        : 17
% 0.20/0.52  # Processed clauses                    : 793
% 0.20/0.52  # ...of these trivial                  : 48
% 0.20/0.52  # ...subsumed                          : 450
% 0.20/0.52  # ...remaining for further processing  : 295
% 0.20/0.52  # Other redundant clauses eliminated   : 30
% 0.20/0.52  # Clauses deleted for lack of memory   : 0
% 0.20/0.52  # Backward-subsumed                    : 19
% 0.20/0.52  # Backward-rewritten                   : 45
% 0.20/0.52  # Generated clauses                    : 7998
% 0.20/0.52  # ...of the previous two non-trivial   : 6873
% 0.20/0.52  # Contextual simplify-reflections      : 2
% 0.20/0.52  # Paramodulations                      : 7968
% 0.20/0.52  # Factorizations                       : 0
% 0.20/0.52  # Equation resolutions                 : 30
% 0.20/0.52  # Propositional unsat checks           : 0
% 0.20/0.52  #    Propositional check models        : 0
% 0.20/0.52  #    Propositional check unsatisfiable : 0
% 0.20/0.52  #    Propositional clauses             : 0
% 0.20/0.52  #    Propositional clauses after purity: 0
% 0.20/0.52  #    Propositional unsat core size     : 0
% 0.20/0.52  #    Propositional preprocessing time  : 0.000
% 0.20/0.52  #    Propositional encoding time       : 0.000
% 0.20/0.52  #    Propositional solver time         : 0.000
% 0.20/0.52  #    Success case prop preproc time    : 0.000
% 0.20/0.52  #    Success case prop encoding time   : 0.000
% 0.20/0.52  #    Success case prop solver time     : 0.000
% 0.20/0.52  # Current number of processed clauses  : 212
% 0.20/0.52  #    Positive orientable unit clauses  : 42
% 0.20/0.52  #    Positive unorientable unit clauses: 12
% 0.20/0.52  #    Negative unit clauses             : 2
% 0.20/0.52  #    Non-unit-clauses                  : 156
% 0.20/0.52  # Current number of unprocessed clauses: 5902
% 0.20/0.52  # ...number of literals in the above   : 12085
% 0.20/0.52  # Current number of archived formulas  : 0
% 0.20/0.52  # Current number of archived clauses   : 83
% 0.20/0.52  # Clause-clause subsumption calls (NU) : 3260
% 0.20/0.52  # Rec. Clause-clause subsumption calls : 2850
% 0.20/0.52  # Non-unit clause-clause subsumptions  : 400
% 0.20/0.52  # Unit Clause-clause subsumption calls : 54
% 0.20/0.52  # Rewrite failures with RHS unbound    : 0
% 0.20/0.52  # BW rewrite match attempts            : 409
% 0.20/0.52  # BW rewrite match successes           : 127
% 0.20/0.52  # Condensation attempts                : 0
% 0.20/0.52  # Condensation successes               : 0
% 0.20/0.52  # Termbank termtop insertions          : 222416
% 0.20/0.52  
% 0.20/0.52  # -------------------------------------------------
% 0.20/0.52  # User time                : 0.168 s
% 0.20/0.52  # System time              : 0.009 s
% 0.20/0.52  # Total time               : 0.177 s
% 0.20/0.52  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
