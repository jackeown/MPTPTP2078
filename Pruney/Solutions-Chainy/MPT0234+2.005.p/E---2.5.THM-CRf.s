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
% DateTime   : Thu Dec  3 10:39:15 EST 2020

% Result     : Theorem 25.59s
% Output     : CNFRefutation 25.59s
% Verified   : 
% Statistics : Number of formulae       :  116 (1382 expanded)
%              Number of clauses        :   69 ( 570 expanded)
%              Number of leaves         :   23 ( 405 expanded)
%              Depth                    :   11
%              Number of atoms          :  143 (1558 expanded)
%              Number of equality atoms :  115 (1351 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( X1 != X2
     => k5_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(t63_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

fof(t83_enumset1,axiom,(
    ! [X1,X2] : k3_enumset1(X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t76_enumset1,axiom,(
    ! [X1] : k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(t93_enumset1,axiom,(
    ! [X1,X2,X3] : k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_enumset1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t60_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t86_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_enumset1)).

fof(t61_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(t96_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( X1 != X2
       => k5_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k2_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t29_zfmisc_1])).

fof(c_0_24,plain,(
    ! [X47,X48,X49,X50,X51,X52,X53,X54] : k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54) = k2_xboole_0(k2_tarski(X47,X48),k4_enumset1(X49,X50,X51,X52,X53,X54)) ),
    inference(variable_rename,[status(thm)],[t63_enumset1])).

fof(c_0_25,plain,(
    ! [X67,X68] : k3_enumset1(X67,X67,X67,X67,X68) = k2_tarski(X67,X68) ),
    inference(variable_rename,[status(thm)],[t83_enumset1])).

fof(c_0_26,plain,(
    ! [X55,X56,X57,X58,X59] : k4_enumset1(X55,X55,X56,X57,X58,X59) = k3_enumset1(X55,X56,X57,X58,X59) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_27,plain,(
    ! [X60,X61,X62,X63,X64,X65] : k5_enumset1(X60,X60,X61,X62,X63,X64,X65) = k4_enumset1(X60,X61,X62,X63,X64,X65) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_28,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_29,negated_conjecture,
    ( esk1_0 != esk2_0
    & k5_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)) != k2_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_30,plain,(
    ! [X66] : k1_enumset1(X66,X66,X66) = k1_tarski(X66) ),
    inference(variable_rename,[status(thm)],[t76_enumset1])).

fof(c_0_31,plain,(
    ! [X74,X75,X76] : k6_enumset1(X74,X74,X74,X74,X74,X74,X75,X76) = k1_enumset1(X74,X75,X76) ),
    inference(variable_rename,[status(thm)],[t93_enumset1])).

cnf(c_0_32,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k2_xboole_0(X27,X28)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_37,plain,(
    ! [X11] : k2_xboole_0(X11,X11) = X11 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_38,plain,(
    ! [X19,X20,X21] : k4_xboole_0(k4_xboole_0(X19,X20),X21) = k4_xboole_0(X19,k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_39,plain,(
    ! [X17,X18] : k4_xboole_0(k2_xboole_0(X17,X18),X18) = k4_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_40,plain,(
    ! [X25,X26] :
      ( ~ r1_tarski(X25,X26)
      | X26 = k2_xboole_0(X25,k4_xboole_0(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

fof(c_0_41,plain,(
    ! [X15,X16] : k2_xboole_0(X15,k4_xboole_0(X16,X15)) = k2_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_42,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_tarski(k4_xboole_0(X22,X23),X24)
      | r1_tarski(X22,k2_xboole_0(X23,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)) != k2_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X4,X5,X6,X7,X8)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_35])).

fof(c_0_48,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39] : k5_enumset1(X33,X34,X35,X36,X37,X38,X39) = k2_xboole_0(k3_enumset1(X33,X34,X35,X36,X37),k2_tarski(X38,X39)) ),
    inference(variable_rename,[status(thm)],[t60_enumset1])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_51,plain,(
    ! [X14] : r1_tarski(k1_xboole_0,X14) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(k2_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)),k2_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) != k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_45]),c_0_33]),c_0_34]),c_0_46]),c_0_46]),c_0_35]),c_0_47]),c_0_47])).

fof(c_0_59,plain,(
    ! [X9,X10] : k5_xboole_0(X9,X10) = k5_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_60,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_61,plain,(
    ! [X69,X70,X71,X72,X73] : k6_enumset1(X69,X69,X69,X69,X70,X71,X72,X73) = k3_enumset1(X69,X70,X71,X72,X73) ),
    inference(variable_rename,[status(thm)],[t86_enumset1])).

fof(c_0_62,plain,(
    ! [X40,X41,X42,X43,X44,X45,X46] : k5_enumset1(X40,X41,X42,X43,X44,X45,X46) = k2_xboole_0(k4_enumset1(X40,X41,X42,X43,X44,X45),k1_tarski(X46)) ),
    inference(variable_rename,[status(thm)],[t61_enumset1])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_52])).

cnf(c_0_66,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_55])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_53]),c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) != k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_50]),c_0_50])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_71,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_72,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_63]),c_0_64])])).

fof(c_0_75,plain,(
    ! [X29,X30] : k2_xboole_0(X29,X30) = k2_xboole_0(k5_xboole_0(X29,X30),k3_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

cnf(c_0_76,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_65]),c_0_55])).

cnf(c_0_77,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

fof(c_0_78,plain,(
    ! [X31,X32] : r1_tarski(k4_xboole_0(X31,X32),k5_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t96_xboole_1])).

cnf(c_0_79,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)) != k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_80,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_71])).

cnf(c_0_81,plain,
    ( k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X2,X3,X4,X5)) = k5_enumset1(X1,X1,X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_34]),c_0_35]),c_0_47])).

cnf(c_0_82,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k2_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X7,X7,X7,X7,X7,X7,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_45]),c_0_46]),c_0_35]),c_0_47])).

fof(c_0_83,plain,(
    ! [X77,X78] :
      ( ( k4_xboole_0(k1_tarski(X77),k1_tarski(X78)) != k1_tarski(X77)
        | X77 != X78 )
      & ( X77 = X78
        | k4_xboole_0(k1_tarski(X77),k1_tarski(X78)) = k1_tarski(X77) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

cnf(c_0_84,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_74])).

cnf(c_0_85,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_86,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_87,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_88,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)) != k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_89,plain,
    ( k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k5_enumset1(X1,X2,X3,X4,X5,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_81]),c_0_50]),c_0_71])).

cnf(c_0_90,plain,
    ( k2_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X7,X7)) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_82,c_0_81])).

cnf(c_0_91,plain,
    ( k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X1,X2)) = k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X4,X5,X6,X7)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_71])).

cnf(c_0_92,plain,
    ( k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X4,X5,X6,X7)) = k5_enumset1(X3,X4,X5,X6,X7,X1,X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_77])).

cnf(c_0_93,plain,
    ( X1 = X2
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_94,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_77])).

cnf(c_0_95,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_86]),c_0_86])).

cnf(c_0_96,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_87])).

cnf(c_0_97,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)) != k5_enumset1(esk1_0,esk1_0,esk2_0,esk1_0,esk2_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_98,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k5_enumset1(X1,X2,X3,X4,X5,X6,X6) ),
    inference(spm,[status(thm)],[c_0_71,c_0_90])).

cnf(c_0_99,plain,
    ( k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X1,X2)) = k5_enumset1(X3,X4,X5,X6,X7,X1,X2) ),
    inference(rw,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_100,plain,
    ( k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X3,X3)) = k5_enumset1(X3,X4,X5,X6,X7,X1,X2) ),
    inference(spm,[status(thm)],[c_0_92,c_0_89])).

cnf(c_0_101,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_87])).

cnf(c_0_102,plain,
    ( X1 = X2
    | k4_xboole_0(k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k2_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))) = k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_47])).

cnf(c_0_103,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_94,c_0_70])).

cnf(c_0_104,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_95])).

cnf(c_0_105,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X1,X2))) = k2_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_96])).

cnf(c_0_106,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)) != k5_enumset1(esk1_0,esk2_0,esk1_0,esk2_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_107,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X4,X5) = k5_enumset1(X1,X2,X3,X4,X5,X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_89]),c_0_100])).

cnf(c_0_108,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X2,X1)) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_70])).

cnf(c_0_109,plain,
    ( k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1)
    | X1 = X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_81]),c_0_81]),c_0_81])).

cnf(c_0_110,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104]),c_0_105])).

cnf(c_0_111,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)) != k5_enumset1(esk1_0,esk2_0,esk1_0,esk2_0,esk1_0,esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_112,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) = k5_enumset1(X2,X2,X2,X2,X2,X1,X1)
    | X2 = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_110]),c_0_71])).

cnf(c_0_113,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X2,X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_98])).

cnf(c_0_114,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_115,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_113]),c_0_89]),c_0_98]),c_0_107])]),c_0_114]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 25.59/25.81  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 25.59/25.81  # and selection function GSelectMinInfpos.
% 25.59/25.81  #
% 25.59/25.81  # Preprocessing time       : 0.027 s
% 25.59/25.81  # Presaturation interreduction done
% 25.59/25.81  
% 25.59/25.81  # Proof found!
% 25.59/25.81  # SZS status Theorem
% 25.59/25.81  # SZS output start CNFRefutation
% 25.59/25.81  fof(t29_zfmisc_1, conjecture, ![X1, X2]:(X1!=X2=>k5_xboole_0(k1_tarski(X1),k1_tarski(X2))=k2_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 25.59/25.81  fof(t63_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 25.59/25.81  fof(t83_enumset1, axiom, ![X1, X2]:k3_enumset1(X1,X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_enumset1)).
% 25.59/25.81  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 25.59/25.81  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 25.59/25.81  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 25.59/25.81  fof(t76_enumset1, axiom, ![X1]:k1_enumset1(X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 25.59/25.81  fof(t93_enumset1, axiom, ![X1, X2, X3]:k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_enumset1)).
% 25.59/25.81  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 25.59/25.81  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 25.59/25.81  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 25.59/25.81  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 25.59/25.81  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 25.59/25.81  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 25.59/25.81  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 25.59/25.81  fof(t60_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 25.59/25.81  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 25.59/25.81  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 25.59/25.81  fof(t86_enumset1, axiom, ![X1, X2, X3, X4, X5]:k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_enumset1)).
% 25.59/25.81  fof(t61_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 25.59/25.81  fof(t93_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_xboole_1)).
% 25.59/25.81  fof(t96_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 25.59/25.81  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 25.59/25.81  fof(c_0_23, negated_conjecture, ~(![X1, X2]:(X1!=X2=>k5_xboole_0(k1_tarski(X1),k1_tarski(X2))=k2_tarski(X1,X2))), inference(assume_negation,[status(cth)],[t29_zfmisc_1])).
% 25.59/25.81  fof(c_0_24, plain, ![X47, X48, X49, X50, X51, X52, X53, X54]:k6_enumset1(X47,X48,X49,X50,X51,X52,X53,X54)=k2_xboole_0(k2_tarski(X47,X48),k4_enumset1(X49,X50,X51,X52,X53,X54)), inference(variable_rename,[status(thm)],[t63_enumset1])).
% 25.59/25.81  fof(c_0_25, plain, ![X67, X68]:k3_enumset1(X67,X67,X67,X67,X68)=k2_tarski(X67,X68), inference(variable_rename,[status(thm)],[t83_enumset1])).
% 25.59/25.81  fof(c_0_26, plain, ![X55, X56, X57, X58, X59]:k4_enumset1(X55,X55,X56,X57,X58,X59)=k3_enumset1(X55,X56,X57,X58,X59), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 25.59/25.81  fof(c_0_27, plain, ![X60, X61, X62, X63, X64, X65]:k5_enumset1(X60,X60,X61,X62,X63,X64,X65)=k4_enumset1(X60,X61,X62,X63,X64,X65), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 25.59/25.81  fof(c_0_28, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 25.59/25.81  fof(c_0_29, negated_conjecture, (esk1_0!=esk2_0&k5_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))!=k2_tarski(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 25.59/25.81  fof(c_0_30, plain, ![X66]:k1_enumset1(X66,X66,X66)=k1_tarski(X66), inference(variable_rename,[status(thm)],[t76_enumset1])).
% 25.59/25.81  fof(c_0_31, plain, ![X74, X75, X76]:k6_enumset1(X74,X74,X74,X74,X74,X74,X75,X76)=k1_enumset1(X74,X75,X76), inference(variable_rename,[status(thm)],[t93_enumset1])).
% 25.59/25.81  cnf(c_0_32, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 25.59/25.81  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 25.59/25.81  cnf(c_0_34, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 25.59/25.81  cnf(c_0_35, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 25.59/25.81  fof(c_0_36, plain, ![X27, X28]:k4_xboole_0(X27,k2_xboole_0(X27,X28))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 25.59/25.81  fof(c_0_37, plain, ![X11]:k2_xboole_0(X11,X11)=X11, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 25.59/25.81  fof(c_0_38, plain, ![X19, X20, X21]:k4_xboole_0(k4_xboole_0(X19,X20),X21)=k4_xboole_0(X19,k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 25.59/25.81  fof(c_0_39, plain, ![X17, X18]:k4_xboole_0(k2_xboole_0(X17,X18),X18)=k4_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 25.59/25.81  fof(c_0_40, plain, ![X25, X26]:(~r1_tarski(X25,X26)|X26=k2_xboole_0(X25,k4_xboole_0(X26,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 25.59/25.81  fof(c_0_41, plain, ![X15, X16]:k2_xboole_0(X15,k4_xboole_0(X16,X15))=k2_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 25.59/25.81  fof(c_0_42, plain, ![X22, X23, X24]:(~r1_tarski(k4_xboole_0(X22,X23),X24)|r1_tarski(X22,k2_xboole_0(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 25.59/25.81  cnf(c_0_43, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 25.59/25.81  cnf(c_0_44, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))!=k2_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 25.59/25.81  cnf(c_0_45, plain, (k1_enumset1(X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 25.59/25.81  cnf(c_0_46, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 25.59/25.81  cnf(c_0_47, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X4,X5,X6,X7,X8))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_35])).
% 25.59/25.81  fof(c_0_48, plain, ![X33, X34, X35, X36, X37, X38, X39]:k5_enumset1(X33,X34,X35,X36,X37,X38,X39)=k2_xboole_0(k3_enumset1(X33,X34,X35,X36,X37),k2_tarski(X38,X39)), inference(variable_rename,[status(thm)],[t60_enumset1])).
% 25.59/25.81  cnf(c_0_49, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 25.59/25.81  cnf(c_0_50, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 25.59/25.81  fof(c_0_51, plain, ![X14]:r1_tarski(k1_xboole_0,X14), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 25.59/25.81  cnf(c_0_52, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 25.59/25.81  cnf(c_0_53, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 25.59/25.81  cnf(c_0_54, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 25.59/25.81  cnf(c_0_55, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 25.59/25.81  cnf(c_0_56, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 25.59/25.81  cnf(c_0_57, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_43])).
% 25.59/25.81  cnf(c_0_58, negated_conjecture, (k5_xboole_0(k2_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)),k2_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))!=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_45]), c_0_33]), c_0_34]), c_0_46]), c_0_46]), c_0_35]), c_0_47]), c_0_47])).
% 25.59/25.81  fof(c_0_59, plain, ![X9, X10]:k5_xboole_0(X9,X10)=k5_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 25.59/25.81  cnf(c_0_60, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 25.59/25.81  fof(c_0_61, plain, ![X69, X70, X71, X72, X73]:k6_enumset1(X69,X69,X69,X69,X70,X71,X72,X73)=k3_enumset1(X69,X70,X71,X72,X73), inference(variable_rename,[status(thm)],[t86_enumset1])).
% 25.59/25.81  fof(c_0_62, plain, ![X40, X41, X42, X43, X44, X45, X46]:k5_enumset1(X40,X41,X42,X43,X44,X45,X46)=k2_xboole_0(k4_enumset1(X40,X41,X42,X43,X44,X45),k1_tarski(X46)), inference(variable_rename,[status(thm)],[t61_enumset1])).
% 25.59/25.81  cnf(c_0_63, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 25.59/25.81  cnf(c_0_64, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 25.59/25.81  cnf(c_0_65, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_52])).
% 25.59/25.81  cnf(c_0_66, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 25.59/25.81  cnf(c_0_67, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_55])).
% 25.59/25.81  cnf(c_0_68, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_53]), c_0_55])).
% 25.59/25.81  cnf(c_0_69, negated_conjecture, (k5_xboole_0(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))!=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_50]), c_0_50])).
% 25.59/25.81  cnf(c_0_70, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 25.59/25.81  cnf(c_0_71, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k5_enumset1(X1,X1,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35])).
% 25.59/25.81  cnf(c_0_72, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 25.59/25.81  cnf(c_0_73, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 25.59/25.81  cnf(c_0_74, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_63]), c_0_64])])).
% 25.59/25.81  fof(c_0_75, plain, ![X29, X30]:k2_xboole_0(X29,X30)=k2_xboole_0(k5_xboole_0(X29,X30),k3_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t93_xboole_1])).
% 25.59/25.81  cnf(c_0_76, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_65]), c_0_55])).
% 25.59/25.81  cnf(c_0_77, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 25.59/25.81  fof(c_0_78, plain, ![X31, X32]:r1_tarski(k4_xboole_0(X31,X32),k5_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t96_xboole_1])).
% 25.59/25.81  cnf(c_0_79, negated_conjecture, (k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))!=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 25.59/25.81  cnf(c_0_80, plain, (k5_enumset1(X1,X1,X1,X1,X2,X1,X2)=k5_enumset1(X1,X1,X1,X1,X1,X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_71])).
% 25.59/25.81  cnf(c_0_81, plain, (k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X2,X3,X4,X5))=k5_enumset1(X1,X1,X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_34]), c_0_35]), c_0_47])).
% 25.59/25.81  cnf(c_0_82, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k2_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X7,X7,X7,X7,X7,X7,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_45]), c_0_46]), c_0_35]), c_0_47])).
% 25.59/25.81  fof(c_0_83, plain, ![X77, X78]:((k4_xboole_0(k1_tarski(X77),k1_tarski(X78))!=k1_tarski(X77)|X77!=X78)&(X77=X78|k4_xboole_0(k1_tarski(X77),k1_tarski(X78))=k1_tarski(X77))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 25.59/25.81  cnf(c_0_84, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_66, c_0_74])).
% 25.59/25.81  cnf(c_0_85, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 25.59/25.81  cnf(c_0_86, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 25.59/25.81  cnf(c_0_87, plain, (r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 25.59/25.81  cnf(c_0_88, negated_conjecture, (k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))!=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_79, c_0_80])).
% 25.59/25.81  cnf(c_0_89, plain, (k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k5_enumset1(X1,X2,X3,X4,X5,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_81]), c_0_50]), c_0_71])).
% 25.59/25.81  cnf(c_0_90, plain, (k2_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X7,X7))=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_82, c_0_81])).
% 25.59/25.81  cnf(c_0_91, plain, (k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X1,X2))=k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X4,X5,X6,X7))), inference(spm,[status(thm)],[c_0_68, c_0_71])).
% 25.59/25.81  cnf(c_0_92, plain, (k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X4,X5,X6,X7))=k5_enumset1(X3,X4,X5,X6,X7,X1,X2)), inference(spm,[status(thm)],[c_0_71, c_0_77])).
% 25.59/25.81  cnf(c_0_93, plain, (X1=X2|k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 25.59/25.81  cnf(c_0_94, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_77])).
% 25.59/25.81  cnf(c_0_95, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_86]), c_0_86])).
% 25.59/25.81  cnf(c_0_96, plain, (r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_56, c_0_87])).
% 25.59/25.81  cnf(c_0_97, negated_conjecture, (k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))!=k5_enumset1(esk1_0,esk1_0,esk2_0,esk1_0,esk2_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[c_0_88, c_0_89])).
% 25.59/25.81  cnf(c_0_98, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k5_enumset1(X1,X2,X3,X4,X5,X6,X6)), inference(spm,[status(thm)],[c_0_71, c_0_90])).
% 25.59/25.81  cnf(c_0_99, plain, (k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X1,X2))=k5_enumset1(X3,X4,X5,X6,X7,X1,X2)), inference(rw,[status(thm)],[c_0_91, c_0_92])).
% 25.59/25.81  cnf(c_0_100, plain, (k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X3,X3))=k5_enumset1(X3,X4,X5,X6,X7,X1,X2)), inference(spm,[status(thm)],[c_0_92, c_0_89])).
% 25.59/25.81  cnf(c_0_101, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_66, c_0_87])).
% 25.59/25.81  cnf(c_0_102, plain, (X1=X2|k4_xboole_0(k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k2_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))=k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_47])).
% 25.59/25.81  cnf(c_0_103, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_94, c_0_70])).
% 25.59/25.81  cnf(c_0_104, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X2,k2_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_77, c_0_95])).
% 25.59/25.81  cnf(c_0_105, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X1,X2)))=k2_xboole_0(X2,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_66, c_0_96])).
% 25.59/25.81  cnf(c_0_106, negated_conjecture, (k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))!=k5_enumset1(esk1_0,esk2_0,esk1_0,esk2_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[c_0_97, c_0_98])).
% 25.59/25.81  cnf(c_0_107, plain, (k5_enumset1(X1,X2,X3,X4,X5,X4,X5)=k5_enumset1(X1,X2,X3,X4,X5,X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_89]), c_0_100])).
% 25.59/25.81  cnf(c_0_108, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X2,X1))=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_101, c_0_70])).
% 25.59/25.81  cnf(c_0_109, plain, (k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)|X1=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_81]), c_0_81]), c_0_81])).
% 25.59/25.81  cnf(c_0_110, plain, (k2_xboole_0(X1,k5_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_104]), c_0_105])).
% 25.59/25.81  cnf(c_0_111, negated_conjecture, (k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))!=k5_enumset1(esk1_0,esk2_0,esk1_0,esk2_0,esk1_0,esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_106, c_0_107])).
% 25.59/25.81  cnf(c_0_112, plain, (k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))=k5_enumset1(X2,X2,X2,X2,X2,X1,X1)|X2=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_110]), c_0_71])).
% 25.59/25.81  cnf(c_0_113, plain, (k5_enumset1(X1,X1,X1,X1,X2,X1,X2)=k5_enumset1(X1,X1,X1,X1,X1,X2,X2)), inference(spm,[status(thm)],[c_0_80, c_0_98])).
% 25.59/25.81  cnf(c_0_114, negated_conjecture, (esk1_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 25.59/25.81  cnf(c_0_115, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_113]), c_0_89]), c_0_98]), c_0_107])]), c_0_114]), ['proof']).
% 25.59/25.81  # SZS output end CNFRefutation
% 25.59/25.81  # Proof object total steps             : 116
% 25.59/25.81  # Proof object clause steps            : 69
% 25.59/25.81  # Proof object formula steps           : 47
% 25.59/25.81  # Proof object conjectures             : 13
% 25.59/25.81  # Proof object clause conjectures      : 10
% 25.59/25.81  # Proof object formula conjectures     : 3
% 25.59/25.81  # Proof object initial clauses used    : 24
% 25.59/25.81  # Proof object initial formulas used   : 23
% 25.59/25.81  # Proof object generating inferences   : 27
% 25.59/25.81  # Proof object simplifying inferences  : 70
% 25.59/25.81  # Training examples: 0 positive, 0 negative
% 25.59/25.81  # Parsed axioms                        : 23
% 25.59/25.81  # Removed by relevancy pruning/SinE    : 0
% 25.59/25.81  # Initial clauses                      : 27
% 25.59/25.81  # Removed in clause preprocessing      : 6
% 25.59/25.81  # Initial clauses in saturation        : 21
% 25.59/25.81  # Processed clauses                    : 52256
% 25.59/25.81  # ...of these trivial                  : 3627
% 25.59/25.81  # ...subsumed                          : 44814
% 25.59/25.81  # ...remaining for further processing  : 3815
% 25.59/25.81  # Other redundant clauses eliminated   : 3
% 25.59/25.81  # Clauses deleted for lack of memory   : 0
% 25.59/25.81  # Backward-subsumed                    : 12
% 25.59/25.81  # Backward-rewritten                   : 199
% 25.59/25.81  # Generated clauses                    : 2684086
% 25.59/25.81  # ...of the previous two non-trivial   : 1894674
% 25.59/25.81  # Contextual simplify-reflections      : 0
% 25.59/25.81  # Paramodulations                      : 2684083
% 25.59/25.81  # Factorizations                       : 0
% 25.59/25.81  # Equation resolutions                 : 3
% 25.59/25.81  # Propositional unsat checks           : 0
% 25.59/25.81  #    Propositional check models        : 0
% 25.59/25.81  #    Propositional check unsatisfiable : 0
% 25.59/25.81  #    Propositional clauses             : 0
% 25.59/25.81  #    Propositional clauses after purity: 0
% 25.59/25.81  #    Propositional unsat core size     : 0
% 25.59/25.81  #    Propositional preprocessing time  : 0.000
% 25.59/25.81  #    Propositional encoding time       : 0.000
% 25.59/25.81  #    Propositional solver time         : 0.000
% 25.59/25.81  #    Success case prop preproc time    : 0.000
% 25.59/25.81  #    Success case prop encoding time   : 0.000
% 25.59/25.81  #    Success case prop solver time     : 0.000
% 25.59/25.81  # Current number of processed clauses  : 3581
% 25.59/25.81  #    Positive orientable unit clauses  : 2373
% 25.59/25.81  #    Positive unorientable unit clauses: 144
% 25.59/25.81  #    Negative unit clauses             : 5
% 25.59/25.81  #    Non-unit-clauses                  : 1059
% 25.59/25.81  # Current number of unprocessed clauses: 1838109
% 25.59/25.81  # ...number of literals in the above   : 2388959
% 25.59/25.81  # Current number of archived formulas  : 0
% 25.59/25.81  # Current number of archived clauses   : 237
% 25.59/25.81  # Clause-clause subsumption calls (NU) : 1767610
% 25.59/25.81  # Rec. Clause-clause subsumption calls : 1767377
% 25.59/25.81  # Non-unit clause-clause subsumptions  : 35095
% 25.59/25.81  # Unit Clause-clause subsumption calls : 23597
% 25.59/25.81  # Rewrite failures with RHS unbound    : 0
% 25.59/25.81  # BW rewrite match attempts            : 68012
% 25.59/25.81  # BW rewrite match successes           : 4069
% 25.59/25.81  # Condensation attempts                : 0
% 25.59/25.81  # Condensation successes               : 0
% 25.59/25.81  # Termbank termtop insertions          : 37387965
% 25.73/25.92  
% 25.73/25.92  # -------------------------------------------------
% 25.73/25.92  # User time                : 24.605 s
% 25.73/25.92  # System time              : 0.946 s
% 25.73/25.92  # Total time               : 25.551 s
% 25.73/25.92  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
