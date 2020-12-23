%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:30 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   98 (4021 expanded)
%              Number of clauses        :   61 (1894 expanded)
%              Number of leaves         :   18 (1063 expanded)
%              Depth                    :   14
%              Number of atoms          :  168 (6479 expanded)
%              Number of equality atoms :  102 (4295 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t70_enumset1,conjecture,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(c_0_18,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( r2_hidden(X21,X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X21,X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X22,X18)
        | r2_hidden(X22,X19)
        | r2_hidden(X22,X20)
        | X20 != k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X23,X24,X25),X25)
        | ~ r2_hidden(esk2_3(X23,X24,X25),X23)
        | r2_hidden(esk2_3(X23,X24,X25),X24)
        | X25 = k4_xboole_0(X23,X24) )
      & ( r2_hidden(esk2_3(X23,X24,X25),X23)
        | r2_hidden(esk2_3(X23,X24,X25),X25)
        | X25 = k4_xboole_0(X23,X24) )
      & ( ~ r2_hidden(esk2_3(X23,X24,X25),X24)
        | r2_hidden(esk2_3(X23,X24,X25),X25)
        | X25 = k4_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_19,plain,(
    ! [X33,X34] : k4_xboole_0(X33,X34) = k5_xboole_0(X33,k3_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_20,plain,(
    ! [X37] : k4_xboole_0(X37,k1_xboole_0) = X37 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_21,plain,(
    ! [X31,X32] :
      ( ( r1_tarski(X31,X32)
        | X31 != X32 )
      & ( r1_tarski(X32,X31)
        | X31 != X32 )
      & ( ~ r1_tarski(X31,X32)
        | ~ r1_tarski(X32,X31)
        | X31 = X32 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_22,plain,(
    ! [X27] : k2_xboole_0(X27,X27) = X27 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_23,plain,(
    ! [X43,X44] : k2_xboole_0(X43,X44) = k5_xboole_0(X43,k4_xboole_0(X44,X43)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_28,plain,(
    ! [X35,X36] :
      ( ~ r1_tarski(X35,X36)
      | k3_xboole_0(X35,X36) = X35 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X38,X39] : k4_xboole_0(X38,k4_xboole_0(X38,X39)) = k3_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_39,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | ~ r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X14)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X15)
        | X16 = k3_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X14)
        | r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k3_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X15)
        | r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k3_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_40,plain,(
    ! [X40,X41,X42] : k5_xboole_0(k5_xboole_0(X40,X41),X42) = k5_xboole_0(X40,k5_xboole_0(X41,X42)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_25])).

cnf(c_0_42,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_25]),c_0_25])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_48,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_34])).

cnf(c_0_51,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_42,c_0_25])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_45])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,X1) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_34]),c_0_45])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_47])).

fof(c_0_56,plain,(
    ! [X51,X52,X53] : k1_enumset1(X51,X52,X53) = k2_xboole_0(k1_tarski(X51),k2_tarski(X52,X53)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_57,plain,(
    ! [X58] : k2_tarski(X58,X58) = k1_tarski(X58) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_58,plain,(
    ! [X45,X46,X47,X48] : k2_enumset1(X45,X46,X47,X48) = k2_xboole_0(k2_tarski(X45,X46),k2_tarski(X47,X48)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,k1_xboole_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_51]),c_0_52])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

fof(c_0_63,plain,(
    ! [X54,X55,X56,X57] : k2_enumset1(X54,X55,X56,X57) = k2_xboole_0(k1_enumset1(X54,X55,X56),k1_tarski(X57)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_64,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_32]),c_0_32]),c_0_25]),c_0_25])).

cnf(c_0_68,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_46])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_61]),c_0_54]),c_0_54]),c_0_62])).

cnf(c_0_70,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_32]),c_0_25])).

cnf(c_0_72,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_32]),c_0_25])).

fof(c_0_73,plain,(
    ! [X49,X50] : k2_tarski(X49,X50) = k2_xboole_0(k1_tarski(X49),k1_tarski(X50)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k3_xboole_0(X1,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_54])).

cnf(c_0_75,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_67]),c_0_68]),c_0_44]),c_0_68]),c_0_44])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_54,c_0_69])).

fof(c_0_77,negated_conjecture,(
    ~ ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(assume_negation,[status(cth)],[t70_enumset1])).

cnf(c_0_78,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_65]),c_0_32]),c_0_25]),c_0_71]),c_0_71]),c_0_72])).

cnf(c_0_79,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_68]),c_0_68])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_35])).

cnf(c_0_82,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_69]),c_0_75])).

cnf(c_0_83,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_76])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_34,c_0_69])).

fof(c_0_85,negated_conjecture,(
    k1_enumset1(esk4_0,esk4_0,esk5_0) != k2_tarski(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_77])])])).

cnf(c_0_86,plain,
    ( k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))))))) = k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_49]),c_0_49])).

cnf(c_0_87,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_65]),c_0_65]),c_0_32]),c_0_25])).

cnf(c_0_88,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_61]),c_0_80]),c_0_80]),c_0_81])).

cnf(c_0_89,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( k1_enumset1(esk4_0,esk4_0,esk5_0) != k2_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_91,plain,
    ( k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X1)))) = k2_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_45]),c_0_54]),c_0_35]),c_0_44]),c_0_87]),c_0_74]),c_0_35]),c_0_88]),c_0_75])).

cnf(c_0_92,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( k5_xboole_0(k2_tarski(esk4_0,esk4_0),k5_xboole_0(k2_tarski(esk4_0,esk5_0),k3_xboole_0(k2_tarski(esk4_0,esk5_0),k2_tarski(esk4_0,esk4_0)))) != k2_tarski(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_90,c_0_71])).

cnf(c_0_94,plain,
    ( k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X1)) = k2_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_91]),c_0_49]),c_0_92]),c_0_82])).

cnf(c_0_95,negated_conjecture,
    ( k5_xboole_0(k2_tarski(esk4_0,esk4_0),k5_xboole_0(k2_tarski(esk4_0,esk5_0),k3_xboole_0(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk5_0)))) != k2_tarski(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_93,c_0_35])).

cnf(c_0_96,plain,
    ( k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X2)) = k2_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96]),c_0_92]),c_0_82])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.58  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.58  # and selection function SelectNegativeLiterals.
% 0.19/0.58  #
% 0.19/0.58  # Preprocessing time       : 0.024 s
% 0.19/0.58  # Presaturation interreduction done
% 0.19/0.58  
% 0.19/0.58  # Proof found!
% 0.19/0.58  # SZS status Theorem
% 0.19/0.58  # SZS output start CNFRefutation
% 0.19/0.58  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.58  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.58  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.58  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.58  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.19/0.58  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.58  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.58  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.58  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.58  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.58  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.58  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.58  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 0.19/0.58  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.58  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 0.19/0.58  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 0.19/0.58  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.19/0.58  fof(t70_enumset1, conjecture, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.58  fof(c_0_18, plain, ![X18, X19, X20, X21, X22, X23, X24, X25]:((((r2_hidden(X21,X18)|~r2_hidden(X21,X20)|X20!=k4_xboole_0(X18,X19))&(~r2_hidden(X21,X19)|~r2_hidden(X21,X20)|X20!=k4_xboole_0(X18,X19)))&(~r2_hidden(X22,X18)|r2_hidden(X22,X19)|r2_hidden(X22,X20)|X20!=k4_xboole_0(X18,X19)))&((~r2_hidden(esk2_3(X23,X24,X25),X25)|(~r2_hidden(esk2_3(X23,X24,X25),X23)|r2_hidden(esk2_3(X23,X24,X25),X24))|X25=k4_xboole_0(X23,X24))&((r2_hidden(esk2_3(X23,X24,X25),X23)|r2_hidden(esk2_3(X23,X24,X25),X25)|X25=k4_xboole_0(X23,X24))&(~r2_hidden(esk2_3(X23,X24,X25),X24)|r2_hidden(esk2_3(X23,X24,X25),X25)|X25=k4_xboole_0(X23,X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.58  fof(c_0_19, plain, ![X33, X34]:k4_xboole_0(X33,X34)=k5_xboole_0(X33,k3_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.58  fof(c_0_20, plain, ![X37]:k4_xboole_0(X37,k1_xboole_0)=X37, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.58  fof(c_0_21, plain, ![X31, X32]:(((r1_tarski(X31,X32)|X31!=X32)&(r1_tarski(X32,X31)|X31!=X32))&(~r1_tarski(X31,X32)|~r1_tarski(X32,X31)|X31=X32)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.58  fof(c_0_22, plain, ![X27]:k2_xboole_0(X27,X27)=X27, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.19/0.58  fof(c_0_23, plain, ![X43, X44]:k2_xboole_0(X43,X44)=k5_xboole_0(X43,k4_xboole_0(X44,X43)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.58  cnf(c_0_24, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.58  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.58  cnf(c_0_26, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.58  fof(c_0_27, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.58  fof(c_0_28, plain, ![X35, X36]:(~r1_tarski(X35,X36)|k3_xboole_0(X35,X36)=X35), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.58  cnf(c_0_29, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.58  fof(c_0_30, plain, ![X38, X39]:k4_xboole_0(X38,k4_xboole_0(X38,X39))=k3_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.58  cnf(c_0_31, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.58  cnf(c_0_32, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.58  cnf(c_0_33, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.58  cnf(c_0_34, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_26, c_0_25])).
% 0.19/0.58  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.58  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.58  cnf(c_0_37, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_29])).
% 0.19/0.58  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.58  fof(c_0_39, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k3_xboole_0(X9,X10))&(r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k3_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|~r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k3_xboole_0(X9,X10)))&((~r2_hidden(esk1_3(X14,X15,X16),X16)|(~r2_hidden(esk1_3(X14,X15,X16),X14)|~r2_hidden(esk1_3(X14,X15,X16),X15))|X16=k3_xboole_0(X14,X15))&((r2_hidden(esk1_3(X14,X15,X16),X14)|r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k3_xboole_0(X14,X15))&(r2_hidden(esk1_3(X14,X15,X16),X15)|r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k3_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.58  fof(c_0_40, plain, ![X40, X41, X42]:k5_xboole_0(k5_xboole_0(X40,X41),X42)=k5_xboole_0(X40,k5_xboole_0(X41,X42)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.58  cnf(c_0_41, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_25])).
% 0.19/0.58  cnf(c_0_42, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.58  cnf(c_0_43, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_33])).
% 0.19/0.58  cnf(c_0_44, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.58  cnf(c_0_45, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.58  cnf(c_0_46, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_25]), c_0_25])).
% 0.19/0.58  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.58  fof(c_0_48, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.58  cnf(c_0_49, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.58  cnf(c_0_50, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_34])).
% 0.19/0.58  cnf(c_0_51, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_42, c_0_25])).
% 0.19/0.58  cnf(c_0_52, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.58  cnf(c_0_53, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_43, c_0_45])).
% 0.19/0.58  cnf(c_0_54, plain, (k5_xboole_0(X1,X1)=k3_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_34]), c_0_45])).
% 0.19/0.58  cnf(c_0_55, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_47])).
% 0.19/0.58  fof(c_0_56, plain, ![X51, X52, X53]:k1_enumset1(X51,X52,X53)=k2_xboole_0(k1_tarski(X51),k2_tarski(X52,X53)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.19/0.58  fof(c_0_57, plain, ![X58]:k2_tarski(X58,X58)=k1_tarski(X58), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.58  fof(c_0_58, plain, ![X45, X46, X47, X48]:k2_enumset1(X45,X46,X47,X48)=k2_xboole_0(k2_tarski(X45,X46),k2_tarski(X47,X48)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.19/0.58  cnf(c_0_59, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.58  cnf(c_0_60, plain, (k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X1))=k5_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.58  cnf(c_0_61, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,k1_xboole_0,X1),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_51]), c_0_52])).
% 0.19/0.58  cnf(c_0_62, plain, (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.19/0.58  fof(c_0_63, plain, ![X54, X55, X56, X57]:k2_enumset1(X54,X55,X56,X57)=k2_xboole_0(k1_enumset1(X54,X55,X56),k1_tarski(X57)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.19/0.58  cnf(c_0_64, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.58  cnf(c_0_65, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.58  cnf(c_0_66, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.58  cnf(c_0_67, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_32]), c_0_32]), c_0_25]), c_0_25])).
% 0.19/0.58  cnf(c_0_68, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k3_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_46])).
% 0.19/0.58  cnf(c_0_69, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_61]), c_0_54]), c_0_54]), c_0_62])).
% 0.19/0.58  cnf(c_0_70, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.58  cnf(c_0_71, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_32]), c_0_25])).
% 0.19/0.58  cnf(c_0_72, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_32]), c_0_25])).
% 0.19/0.58  fof(c_0_73, plain, ![X49, X50]:k2_tarski(X49,X50)=k2_xboole_0(k1_tarski(X49),k1_tarski(X50)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.19/0.58  cnf(c_0_74, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(k3_xboole_0(X1,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_49, c_0_54])).
% 0.19/0.58  cnf(c_0_75, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_67]), c_0_68]), c_0_44]), c_0_68]), c_0_44])).
% 0.19/0.58  cnf(c_0_76, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_54, c_0_69])).
% 0.19/0.58  fof(c_0_77, negated_conjecture, ~(![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(assume_negation,[status(cth)],[t70_enumset1])).
% 0.19/0.58  cnf(c_0_78, plain, (k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2))))=k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_65]), c_0_32]), c_0_25]), c_0_71]), c_0_71]), c_0_72])).
% 0.19/0.58  cnf(c_0_79, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.58  cnf(c_0_80, plain, (k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k3_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_68]), c_0_68])).
% 0.19/0.58  cnf(c_0_81, plain, (~r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_62, c_0_35])).
% 0.19/0.58  cnf(c_0_82, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_69]), c_0_75])).
% 0.19/0.58  cnf(c_0_83, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_76])).
% 0.19/0.58  cnf(c_0_84, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_34, c_0_69])).
% 0.19/0.58  fof(c_0_85, negated_conjecture, k1_enumset1(esk4_0,esk4_0,esk5_0)!=k2_tarski(esk4_0,esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_77])])])).
% 0.19/0.58  cnf(c_0_86, plain, (k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)),k5_xboole_0(k2_tarski(X4,X4),k3_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))))))))=k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_49]), c_0_49])).
% 0.19/0.58  cnf(c_0_87, plain, (k2_tarski(X1,X2)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_65]), c_0_65]), c_0_32]), c_0_25])).
% 0.19/0.58  cnf(c_0_88, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_61]), c_0_80]), c_0_80]), c_0_81])).
% 0.19/0.58  cnf(c_0_89, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])).
% 0.19/0.58  cnf(c_0_90, negated_conjecture, (k1_enumset1(esk4_0,esk4_0,esk5_0)!=k2_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.19/0.58  cnf(c_0_91, plain, (k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X1))))=k2_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_45]), c_0_54]), c_0_35]), c_0_44]), c_0_87]), c_0_74]), c_0_35]), c_0_88]), c_0_75])).
% 0.19/0.58  cnf(c_0_92, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_82, c_0_89])).
% 0.19/0.58  cnf(c_0_93, negated_conjecture, (k5_xboole_0(k2_tarski(esk4_0,esk4_0),k5_xboole_0(k2_tarski(esk4_0,esk5_0),k3_xboole_0(k2_tarski(esk4_0,esk5_0),k2_tarski(esk4_0,esk4_0))))!=k2_tarski(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_90, c_0_71])).
% 0.19/0.58  cnf(c_0_94, plain, (k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X1))=k2_tarski(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_91]), c_0_49]), c_0_92]), c_0_82])).
% 0.19/0.58  cnf(c_0_95, negated_conjecture, (k5_xboole_0(k2_tarski(esk4_0,esk4_0),k5_xboole_0(k2_tarski(esk4_0,esk5_0),k3_xboole_0(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk5_0))))!=k2_tarski(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_93, c_0_35])).
% 0.19/0.58  cnf(c_0_96, plain, (k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X2))=k2_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_35, c_0_94])).
% 0.19/0.58  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96]), c_0_92]), c_0_82])]), ['proof']).
% 0.19/0.58  # SZS output end CNFRefutation
% 0.19/0.58  # Proof object total steps             : 98
% 0.19/0.58  # Proof object clause steps            : 61
% 0.19/0.58  # Proof object formula steps           : 37
% 0.19/0.58  # Proof object conjectures             : 7
% 0.19/0.58  # Proof object clause conjectures      : 4
% 0.19/0.58  # Proof object formula conjectures     : 3
% 0.19/0.58  # Proof object initial clauses used    : 19
% 0.19/0.58  # Proof object initial formulas used   : 18
% 0.19/0.58  # Proof object generating inferences   : 21
% 0.19/0.58  # Proof object simplifying inferences  : 68
% 0.19/0.58  # Training examples: 0 positive, 0 negative
% 0.19/0.58  # Parsed axioms                        : 19
% 0.19/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.58  # Initial clauses                      : 32
% 0.19/0.58  # Removed in clause preprocessing      : 5
% 0.19/0.58  # Initial clauses in saturation        : 27
% 0.19/0.58  # Processed clauses                    : 1017
% 0.19/0.58  # ...of these trivial                  : 72
% 0.19/0.58  # ...subsumed                          : 720
% 0.19/0.58  # ...remaining for further processing  : 225
% 0.19/0.58  # Other redundant clauses eliminated   : 140
% 0.19/0.58  # Clauses deleted for lack of memory   : 0
% 0.19/0.58  # Backward-subsumed                    : 5
% 0.19/0.58  # Backward-rewritten                   : 57
% 0.19/0.58  # Generated clauses                    : 13517
% 0.19/0.58  # ...of the previous two non-trivial   : 12425
% 0.19/0.58  # Contextual simplify-reflections      : 1
% 0.19/0.58  # Paramodulations                      : 13377
% 0.19/0.58  # Factorizations                       : 0
% 0.19/0.58  # Equation resolutions                 : 140
% 0.19/0.58  # Propositional unsat checks           : 0
% 0.19/0.58  #    Propositional check models        : 0
% 0.19/0.58  #    Propositional check unsatisfiable : 0
% 0.19/0.58  #    Propositional clauses             : 0
% 0.19/0.58  #    Propositional clauses after purity: 0
% 0.19/0.58  #    Propositional unsat core size     : 0
% 0.19/0.58  #    Propositional preprocessing time  : 0.000
% 0.19/0.58  #    Propositional encoding time       : 0.000
% 0.19/0.58  #    Propositional solver time         : 0.000
% 0.19/0.58  #    Success case prop preproc time    : 0.000
% 0.19/0.58  #    Success case prop encoding time   : 0.000
% 0.19/0.58  #    Success case prop solver time     : 0.000
% 0.19/0.58  # Current number of processed clauses  : 129
% 0.19/0.58  #    Positive orientable unit clauses  : 33
% 0.19/0.58  #    Positive unorientable unit clauses: 5
% 0.19/0.58  #    Negative unit clauses             : 1
% 0.19/0.58  #    Non-unit-clauses                  : 90
% 0.19/0.58  # Current number of unprocessed clauses: 11323
% 0.19/0.58  # ...number of literals in the above   : 37721
% 0.19/0.58  # Current number of archived formulas  : 0
% 0.19/0.58  # Current number of archived clauses   : 93
% 0.19/0.58  # Clause-clause subsumption calls (NU) : 4661
% 0.19/0.58  # Rec. Clause-clause subsumption calls : 3719
% 0.19/0.58  # Non-unit clause-clause subsumptions  : 541
% 0.19/0.58  # Unit Clause-clause subsumption calls : 366
% 0.19/0.58  # Rewrite failures with RHS unbound    : 0
% 0.19/0.58  # BW rewrite match attempts            : 403
% 0.19/0.58  # BW rewrite match successes           : 161
% 0.19/0.58  # Condensation attempts                : 0
% 0.19/0.58  # Condensation successes               : 0
% 0.19/0.58  # Termbank termtop insertions          : 395930
% 0.19/0.58  
% 0.19/0.58  # -------------------------------------------------
% 0.19/0.58  # User time                : 0.223 s
% 0.19/0.58  # System time              : 0.012 s
% 0.19/0.58  # Total time               : 0.235 s
% 0.19/0.58  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
