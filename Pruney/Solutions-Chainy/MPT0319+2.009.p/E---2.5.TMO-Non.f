%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:57 EST 2020

% Result     : Timeout 58.12s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   89 ( 828 expanded)
%              Number of clauses        :   56 ( 369 expanded)
%              Number of leaves         :   16 ( 228 expanded)
%              Depth                    :   13
%              Number of atoms          :  137 (1057 expanded)
%              Number of equality atoms :   79 ( 759 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t96_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t125_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t131_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( X1 != X2
     => ( r1_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X4))
        & r1_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X4,k1_tarski(X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_zfmisc_1)).

fof(c_0_16,plain,(
    ! [X5,X6] :
      ( ( ~ r1_xboole_0(X5,X6)
        | k3_xboole_0(X5,X6) = k1_xboole_0 )
      & ( k3_xboole_0(X5,X6) != k1_xboole_0
        | r1_xboole_0(X5,X6) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_17,plain,(
    ! [X19,X20] : k3_xboole_0(X19,X20) = k5_xboole_0(k5_xboole_0(X19,X20),k2_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_18,plain,(
    ! [X8,X9] : r1_xboole_0(k3_xboole_0(X8,X9),k5_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

fof(c_0_19,plain,(
    ! [X16] : k4_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_20,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,plain,(
    ! [X15] : k3_xboole_0(X15,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_22,plain,(
    ! [X12,X13,X14] :
      ( ( r1_tarski(X12,X13)
        | ~ r1_tarski(X12,k4_xboole_0(X13,X14)) )
      & ( r1_xboole_0(X12,X14)
        | ~ r1_tarski(X12,k4_xboole_0(X13,X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X7] : k3_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( r1_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_24])).

cnf(c_0_34,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_28,c_0_24])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_37,plain,(
    ! [X21,X22] : r1_tarski(k4_xboole_0(X21,X22),k5_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t96_xboole_1])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X3,X2),k2_xboole_0(X3,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_27]),c_0_24])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k5_xboole_0(X1,X2)),k2_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_27]),c_0_24])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k2_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_36,c_0_24])).

cnf(c_0_43,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_44,plain,(
    ! [X17,X18] :
      ( ( ~ r1_xboole_0(X17,X18)
        | k4_xboole_0(X17,X18) = X17 )
      & ( k4_xboole_0(X17,X18) != X17
        | r1_xboole_0(X17,X18) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_45,plain,(
    ! [X33,X34] :
      ( ( k4_xboole_0(k1_tarski(X33),k1_tarski(X34)) != k1_tarski(X33)
        | X33 != X34 )
      & ( X33 = X34
        | k4_xboole_0(k1_tarski(X33),k1_tarski(X34)) = k1_tarski(X33) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_46,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_47,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_48,plain,(
    ! [X30,X31,X32] :
      ( k2_zfmisc_1(k4_xboole_0(X30,X31),X32) = k4_xboole_0(k2_zfmisc_1(X30,X32),k2_zfmisc_1(X31,X32))
      & k2_zfmisc_1(X32,k4_xboole_0(X30,X31)) = k4_xboole_0(k2_zfmisc_1(X32,X30),k2_zfmisc_1(X32,X31)) ) ),
    inference(variable_rename,[status(thm)],[t125_zfmisc_1])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_27]),c_0_24])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( X1 = X2
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_42])).

cnf(c_0_58,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_42])).

cnf(c_0_59,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_60,plain,(
    ! [X26,X27,X28,X29] : k2_zfmisc_1(k3_xboole_0(X26,X27),k3_xboole_0(X28,X29)) = k3_xboole_0(k2_zfmisc_1(X26,X28),k2_zfmisc_1(X27,X29)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))) != X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_27]),c_0_24])).

cnf(c_0_62,plain,
    ( X1 = X2
    | k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)))) = k1_enumset1(X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_55]),c_0_27]),c_0_24])).

cnf(c_0_63,plain,
    ( k2_zfmisc_1(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))) = k5_xboole_0(k2_zfmisc_1(X1,X2),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)),k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_27]),c_0_27]),c_0_24]),c_0_24])).

cnf(c_0_64,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X3) = k5_xboole_0(k2_zfmisc_1(X1,X3),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)),k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_27]),c_0_27]),c_0_24]),c_0_24])).

fof(c_0_66,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( X1 != X2
       => ( r1_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X4))
          & r1_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X4,k1_tarski(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t131_zfmisc_1])).

cnf(c_0_67,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( X1 = X2
    | r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(X1,k5_xboole_0(X2,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_42]),c_0_42])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_64]),c_0_42])).

cnf(c_0_71,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,X1),X2) = k2_zfmisc_1(X1,k5_xboole_0(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_65]),c_0_42]),c_0_42])).

fof(c_0_72,negated_conjecture,
    ( esk1_0 != esk2_0
    & ( ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(esk1_0),esk3_0),k2_zfmisc_1(k1_tarski(esk2_0),esk4_0))
      | ~ r1_xboole_0(k2_zfmisc_1(esk3_0,k1_tarski(esk1_0)),k2_zfmisc_1(esk4_0,k1_tarski(esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_66])])])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_74,plain,
    ( k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X3,X4),k2_xboole_0(X3,X4))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)),k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_75,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2))) = k1_xboole_0
    | X1 = X2 ),
    inference(spm,[status(thm)],[c_0_31,c_0_68])).

cnf(c_0_76,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_70])).

cnf(c_0_77,plain,
    ( k2_zfmisc_1(k1_xboole_0,k5_xboole_0(X1,X1)) = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_40])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(esk1_0),esk3_0),k2_zfmisc_1(k1_tarski(esk2_0),esk4_0))
    | ~ r1_xboole_0(k2_zfmisc_1(esk3_0,k1_tarski(esk1_0)),k2_zfmisc_1(esk4_0,k1_tarski(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_79,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_73,c_0_24])).

cnf(c_0_80,plain,
    ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)),k2_zfmisc_1(X3,k1_enumset1(X4,X4,X4))),k2_xboole_0(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)),k2_zfmisc_1(X3,k1_enumset1(X4,X4,X4)))) = k1_xboole_0
    | X2 = X4 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_81,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_70]),c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(esk3_0,k1_enumset1(esk1_0,esk1_0,esk1_0)),k2_zfmisc_1(esk4_0,k1_enumset1(esk2_0,esk2_0,esk2_0)))
    | ~ r1_xboole_0(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),esk3_0),k2_zfmisc_1(k1_enumset1(esk2_0,esk2_0,esk2_0),esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_55]),c_0_55])).

cnf(c_0_83,plain,
    ( X1 = X2
    | r1_xboole_0(k2_zfmisc_1(X3,k1_enumset1(X1,X1,X1)),k2_zfmisc_1(X4,k1_enumset1(X2,X2,X2))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_85,plain,
    ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2),k2_zfmisc_1(k1_enumset1(X3,X3,X3),X4)),k2_xboole_0(k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2),k2_zfmisc_1(k1_enumset1(X3,X3,X3),X4))) = k1_xboole_0
    | X1 = X3 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),esk3_0),k2_zfmisc_1(k1_enumset1(esk2_0,esk2_0,esk2_0),esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])).

cnf(c_0_87,plain,
    ( X1 = X2
    | r1_xboole_0(k2_zfmisc_1(k1_enumset1(X1,X1,X1),X3),k2_zfmisc_1(k1_enumset1(X2,X2,X2),X4)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n016.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 12:07:19 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 58.12/58.32  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 58.12/58.32  # and selection function SelectCQIArNpEqFirst.
% 58.12/58.32  #
% 58.12/58.32  # Preprocessing time       : 0.027 s
% 58.12/58.32  # Presaturation interreduction done
% 58.12/58.32  
% 58.12/58.32  # Proof found!
% 58.12/58.32  # SZS status Theorem
% 58.12/58.32  # SZS output start CNFRefutation
% 58.12/58.32  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 58.12/58.32  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 58.12/58.32  fof(l97_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 58.12/58.32  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 58.12/58.32  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 58.12/58.32  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 58.12/58.32  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 58.12/58.32  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 58.12/58.32  fof(t96_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 58.12/58.32  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 58.12/58.32  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 58.12/58.32  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 58.12/58.32  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 58.12/58.32  fof(t125_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k4_xboole_0(X1,X2))=k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 58.12/58.32  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 58.12/58.32  fof(t131_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(X1!=X2=>(r1_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X4))&r1_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X4,k1_tarski(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_zfmisc_1)).
% 58.12/58.32  fof(c_0_16, plain, ![X5, X6]:((~r1_xboole_0(X5,X6)|k3_xboole_0(X5,X6)=k1_xboole_0)&(k3_xboole_0(X5,X6)!=k1_xboole_0|r1_xboole_0(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 58.12/58.32  fof(c_0_17, plain, ![X19, X20]:k3_xboole_0(X19,X20)=k5_xboole_0(k5_xboole_0(X19,X20),k2_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 58.12/58.32  fof(c_0_18, plain, ![X8, X9]:r1_xboole_0(k3_xboole_0(X8,X9),k5_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[l97_xboole_1])).
% 58.12/58.32  fof(c_0_19, plain, ![X16]:k4_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t3_boole])).
% 58.12/58.32  fof(c_0_20, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 58.12/58.32  fof(c_0_21, plain, ![X15]:k3_xboole_0(X15,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 58.12/58.32  fof(c_0_22, plain, ![X12, X13, X14]:((r1_tarski(X12,X13)|~r1_tarski(X12,k4_xboole_0(X13,X14)))&(r1_xboole_0(X12,X14)|~r1_tarski(X12,k4_xboole_0(X13,X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 58.12/58.32  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 58.12/58.32  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 58.12/58.32  cnf(c_0_25, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 58.12/58.32  cnf(c_0_26, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 58.12/58.32  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 58.12/58.32  cnf(c_0_28, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 58.12/58.32  fof(c_0_29, plain, ![X7]:k3_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 58.12/58.32  cnf(c_0_30, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 58.12/58.32  cnf(c_0_31, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 58.12/58.32  cnf(c_0_32, plain, (r1_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_25, c_0_24])).
% 58.12/58.32  cnf(c_0_33, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_24])).
% 58.12/58.32  cnf(c_0_34, plain, (k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_28, c_0_24])).
% 58.12/58.32  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 58.12/58.32  cnf(c_0_36, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 58.12/58.32  fof(c_0_37, plain, ![X21, X22]:r1_tarski(k4_xboole_0(X21,X22),k5_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t96_xboole_1])).
% 58.12/58.32  cnf(c_0_38, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X3,X2),k2_xboole_0(X3,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_27]), c_0_24])).
% 58.12/58.32  cnf(c_0_39, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k5_xboole_0(X1,X2)),k2_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 58.12/58.32  cnf(c_0_40, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 58.12/58.32  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_27]), c_0_24])).
% 58.12/58.32  cnf(c_0_42, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k2_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_36, c_0_24])).
% 58.12/58.32  cnf(c_0_43, plain, (r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 58.12/58.32  fof(c_0_44, plain, ![X17, X18]:((~r1_xboole_0(X17,X18)|k4_xboole_0(X17,X18)=X17)&(k4_xboole_0(X17,X18)!=X17|r1_xboole_0(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 58.12/58.32  fof(c_0_45, plain, ![X33, X34]:((k4_xboole_0(k1_tarski(X33),k1_tarski(X34))!=k1_tarski(X33)|X33!=X34)&(X33=X34|k4_xboole_0(k1_tarski(X33),k1_tarski(X34))=k1_tarski(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 58.12/58.32  fof(c_0_46, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 58.12/58.32  fof(c_0_47, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 58.12/58.32  fof(c_0_48, plain, ![X30, X31, X32]:(k2_zfmisc_1(k4_xboole_0(X30,X31),X32)=k4_xboole_0(k2_zfmisc_1(X30,X32),k2_zfmisc_1(X31,X32))&k2_zfmisc_1(X32,k4_xboole_0(X30,X31))=k4_xboole_0(k2_zfmisc_1(X32,X30),k2_zfmisc_1(X32,X31))), inference(variable_rename,[status(thm)],[t125_zfmisc_1])).
% 58.12/58.32  cnf(c_0_49, plain, (r1_xboole_0(X1,k5_xboole_0(X2,X3))|~r1_tarski(X1,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 58.12/58.32  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k5_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 58.12/58.32  cnf(c_0_51, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_27]), c_0_24])).
% 58.12/58.32  cnf(c_0_52, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_44])).
% 58.12/58.32  cnf(c_0_53, plain, (X1=X2|k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 58.12/58.32  cnf(c_0_54, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 58.12/58.32  cnf(c_0_55, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 58.12/58.32  cnf(c_0_56, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 58.12/58.32  cnf(c_0_57, plain, (r1_xboole_0(X1,k5_xboole_0(X2,X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_49, c_0_42])).
% 58.12/58.32  cnf(c_0_58, plain, (r1_tarski(k5_xboole_0(X1,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_42])).
% 58.12/58.32  cnf(c_0_59, plain, (k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 58.12/58.32  fof(c_0_60, plain, ![X26, X27, X28, X29]:k2_zfmisc_1(k3_xboole_0(X26,X27),k3_xboole_0(X28,X29))=k3_xboole_0(k2_zfmisc_1(X26,X28),k2_zfmisc_1(X27,X29)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 58.12/58.32  cnf(c_0_61, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))!=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_27]), c_0_24])).
% 58.12/58.32  cnf(c_0_62, plain, (X1=X2|k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2))))=k1_enumset1(X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_54]), c_0_54]), c_0_55]), c_0_55]), c_0_55]), c_0_27]), c_0_24])).
% 58.12/58.32  cnf(c_0_63, plain, (k2_zfmisc_1(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))))=k5_xboole_0(k2_zfmisc_1(X1,X2),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)),k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_27]), c_0_27]), c_0_24]), c_0_24])).
% 58.12/58.32  cnf(c_0_64, plain, (r1_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 58.12/58.32  cnf(c_0_65, plain, (k2_zfmisc_1(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X3)=k5_xboole_0(k2_zfmisc_1(X1,X3),k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)),k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_27]), c_0_27]), c_0_24]), c_0_24])).
% 58.12/58.32  fof(c_0_66, negated_conjecture, ~(![X1, X2, X3, X4]:(X1!=X2=>(r1_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X4))&r1_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X4,k1_tarski(X2)))))), inference(assume_negation,[status(cth)],[t131_zfmisc_1])).
% 58.12/58.32  cnf(c_0_67, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 58.12/58.32  cnf(c_0_68, plain, (X1=X2|r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 58.12/58.32  cnf(c_0_69, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2))=k2_zfmisc_1(X1,k5_xboole_0(X2,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_42]), c_0_42])).
% 58.12/58.32  cnf(c_0_70, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_64]), c_0_42])).
% 58.12/58.32  cnf(c_0_71, plain, (k2_zfmisc_1(k5_xboole_0(X1,X1),X2)=k2_zfmisc_1(X1,k5_xboole_0(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_65]), c_0_42]), c_0_42])).
% 58.12/58.32  fof(c_0_72, negated_conjecture, (esk1_0!=esk2_0&(~r1_xboole_0(k2_zfmisc_1(k1_tarski(esk1_0),esk3_0),k2_zfmisc_1(k1_tarski(esk2_0),esk4_0))|~r1_xboole_0(k2_zfmisc_1(esk3_0,k1_tarski(esk1_0)),k2_zfmisc_1(esk4_0,k1_tarski(esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_66])])])).
% 58.12/58.32  cnf(c_0_73, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 58.12/58.32  cnf(c_0_74, plain, (k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X3,X4),k2_xboole_0(X3,X4)))=k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)),k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_24]), c_0_24]), c_0_24])).
% 58.12/58.32  cnf(c_0_75, plain, (k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)))=k1_xboole_0|X1=X2), inference(spm,[status(thm)],[c_0_31, c_0_68])).
% 58.12/58.32  cnf(c_0_76, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_70])).
% 58.12/58.32  cnf(c_0_77, plain, (k2_zfmisc_1(k1_xboole_0,k5_xboole_0(X1,X1))=k2_zfmisc_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_71, c_0_40])).
% 58.12/58.32  cnf(c_0_78, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(k1_tarski(esk1_0),esk3_0),k2_zfmisc_1(k1_tarski(esk2_0),esk4_0))|~r1_xboole_0(k2_zfmisc_1(esk3_0,k1_tarski(esk1_0)),k2_zfmisc_1(esk4_0,k1_tarski(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 58.12/58.32  cnf(c_0_79, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_73, c_0_24])).
% 58.12/58.32  cnf(c_0_80, plain, (k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)),k2_zfmisc_1(X3,k1_enumset1(X4,X4,X4))),k2_xboole_0(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)),k2_zfmisc_1(X3,k1_enumset1(X4,X4,X4))))=k1_xboole_0|X2=X4), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 58.12/58.32  cnf(c_0_81, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_70]), c_0_76])).
% 58.12/58.32  cnf(c_0_82, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(esk3_0,k1_enumset1(esk1_0,esk1_0,esk1_0)),k2_zfmisc_1(esk4_0,k1_enumset1(esk2_0,esk2_0,esk2_0)))|~r1_xboole_0(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),esk3_0),k2_zfmisc_1(k1_enumset1(esk2_0,esk2_0,esk2_0),esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_55]), c_0_55]), c_0_55]), c_0_55])).
% 58.12/58.32  cnf(c_0_83, plain, (X1=X2|r1_xboole_0(k2_zfmisc_1(X3,k1_enumset1(X1,X1,X1)),k2_zfmisc_1(X4,k1_enumset1(X2,X2,X2)))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 58.12/58.32  cnf(c_0_84, negated_conjecture, (esk1_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_72])).
% 58.12/58.32  cnf(c_0_85, plain, (k5_xboole_0(k5_xboole_0(k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2),k2_zfmisc_1(k1_enumset1(X3,X3,X3),X4)),k2_xboole_0(k2_zfmisc_1(k1_enumset1(X1,X1,X1),X2),k2_zfmisc_1(k1_enumset1(X3,X3,X3),X4)))=k1_xboole_0|X1=X3), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_81])).
% 58.12/58.32  cnf(c_0_86, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),esk3_0),k2_zfmisc_1(k1_enumset1(esk2_0,esk2_0,esk2_0),esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])).
% 58.12/58.32  cnf(c_0_87, plain, (X1=X2|r1_xboole_0(k2_zfmisc_1(k1_enumset1(X1,X1,X1),X3),k2_zfmisc_1(k1_enumset1(X2,X2,X2),X4))), inference(spm,[status(thm)],[c_0_79, c_0_85])).
% 58.12/58.32  cnf(c_0_88, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_84]), ['proof']).
% 58.12/58.32  # SZS output end CNFRefutation
% 58.12/58.32  # Proof object total steps             : 89
% 58.12/58.32  # Proof object clause steps            : 56
% 58.12/58.32  # Proof object formula steps           : 33
% 58.12/58.32  # Proof object conjectures             : 8
% 58.12/58.32  # Proof object clause conjectures      : 5
% 58.12/58.32  # Proof object formula conjectures     : 3
% 58.12/58.32  # Proof object initial clauses used    : 20
% 58.12/58.32  # Proof object initial formulas used   : 16
% 58.12/58.32  # Proof object generating inferences   : 18
% 58.12/58.32  # Proof object simplifying inferences  : 57
% 58.12/58.32  # Training examples: 0 positive, 0 negative
% 58.12/58.32  # Parsed axioms                        : 16
% 58.12/58.32  # Removed by relevancy pruning/SinE    : 0
% 58.12/58.32  # Initial clauses                      : 22
% 58.12/58.32  # Removed in clause preprocessing      : 4
% 58.12/58.32  # Initial clauses in saturation        : 18
% 58.12/58.32  # Processed clauses                    : 23114
% 58.12/58.32  # ...of these trivial                  : 517
% 58.12/58.32  # ...subsumed                          : 19504
% 58.12/58.32  # ...remaining for further processing  : 3093
% 58.12/58.32  # Other redundant clauses eliminated   : 8
% 58.12/58.32  # Clauses deleted for lack of memory   : 0
% 58.12/58.32  # Backward-subsumed                    : 37
% 58.12/58.32  # Backward-rewritten                   : 334
% 58.12/58.32  # Generated clauses                    : 1615947
% 58.12/58.32  # ...of the previous two non-trivial   : 1457732
% 58.12/58.32  # Contextual simplify-reflections      : 0
% 58.12/58.32  # Paramodulations                      : 1615939
% 58.12/58.32  # Factorizations                       : 0
% 58.12/58.32  # Equation resolutions                 : 8
% 58.12/58.32  # Propositional unsat checks           : 0
% 58.12/58.32  #    Propositional check models        : 0
% 58.12/58.32  #    Propositional check unsatisfiable : 0
% 58.12/58.32  #    Propositional clauses             : 0
% 58.12/58.32  #    Propositional clauses after purity: 0
% 58.12/58.32  #    Propositional unsat core size     : 0
% 58.12/58.32  #    Propositional preprocessing time  : 0.000
% 58.12/58.32  #    Propositional encoding time       : 0.000
% 58.12/58.32  #    Propositional solver time         : 0.000
% 58.12/58.32  #    Success case prop preproc time    : 0.000
% 58.12/58.32  #    Success case prop encoding time   : 0.000
% 58.12/58.32  #    Success case prop solver time     : 0.000
% 58.12/58.32  # Current number of processed clauses  : 2702
% 58.12/58.32  #    Positive orientable unit clauses  : 468
% 58.12/58.32  #    Positive unorientable unit clauses: 20
% 58.12/58.32  #    Negative unit clauses             : 3
% 58.12/58.32  #    Non-unit-clauses                  : 2211
% 58.12/58.32  # Current number of unprocessed clauses: 1429623
% 58.12/58.32  # ...number of literals in the above   : 2913852
% 58.12/58.32  # Current number of archived formulas  : 0
% 58.12/58.32  # Current number of archived clauses   : 393
% 58.12/58.32  # Clause-clause subsumption calls (NU) : 706511
% 58.12/58.32  # Rec. Clause-clause subsumption calls : 652331
% 58.12/58.32  # Non-unit clause-clause subsumptions  : 19541
% 58.12/58.32  # Unit Clause-clause subsumption calls : 3345
% 58.12/58.32  # Rewrite failures with RHS unbound    : 0
% 58.12/58.32  # BW rewrite match attempts            : 7850
% 58.12/58.32  # BW rewrite match successes           : 102
% 58.12/58.32  # Condensation attempts                : 0
% 58.12/58.32  # Condensation successes               : 0
% 58.12/58.32  # Termbank termtop insertions          : 423395245
% 58.19/58.39  
% 58.19/58.39  # -------------------------------------------------
% 58.19/58.39  # User time                : 57.155 s
% 58.19/58.39  # System time              : 0.904 s
% 58.19/58.39  # Total time               : 58.059 s
% 58.19/58.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
