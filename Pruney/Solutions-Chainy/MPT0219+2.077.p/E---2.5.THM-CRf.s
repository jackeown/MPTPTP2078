%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:28 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 (2589 expanded)
%              Number of clauses        :   51 (1195 expanded)
%              Number of leaves         :   18 ( 695 expanded)
%              Depth                    :   18
%              Number of atoms          :  204 (3039 expanded)
%              Number of equality atoms :  166 (2580 expanded)
%              Maximal formula depth    :   52 (   4 average)
%              Maximal clause size      :   76 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t13_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t134_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

fof(d7_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( X10 = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)
    <=> ! [X11] :
          ( r2_hidden(X11,X10)
        <=> ~ ( X11 != X1
              & X11 != X2
              & X11 != X3
              & X11 != X4
              & X11 != X5
              & X11 != X6
              & X11 != X7
              & X11 != X8
              & X11 != X9 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_enumset1)).

fof(c_0_18,plain,(
    ! [X26,X27] : k2_xboole_0(X26,X27) = k5_xboole_0(X26,k4_xboole_0(X27,X26)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_19,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_20,plain,(
    ! [X21,X22] : r1_tarski(X21,k2_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X23,X24,X25] : k5_xboole_0(k5_xboole_0(X23,X24),X25) = k5_xboole_0(X23,k5_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_24,plain,(
    ! [X20] : k5_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_25,plain,(
    ! [X18,X19] : k3_xboole_0(X18,k2_xboole_0(X18,X19)) = X18 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_26,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(X14,X15) != k1_xboole_0
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | k4_xboole_0(X14,X15) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_31,c_0_28])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_22])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t13_zfmisc_1])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

fof(c_0_41,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

fof(c_0_42,plain,(
    ! [X60] : k2_tarski(X60,X60) = k1_tarski(X60) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_43,plain,(
    ! [X61,X62] : k1_enumset1(X61,X61,X62) = k2_tarski(X61,X62) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_44,plain,(
    ! [X63,X64,X65] : k2_enumset1(X63,X63,X64,X65) = k1_enumset1(X63,X64,X65) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_45,plain,(
    ! [X66,X67,X68,X69] : k3_enumset1(X66,X66,X67,X68,X69) = k2_enumset1(X66,X67,X68,X69) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_46,plain,(
    ! [X70,X71,X72,X73,X74] : k4_enumset1(X70,X70,X71,X72,X73,X74) = k3_enumset1(X70,X71,X72,X73,X74) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_47,plain,(
    ! [X75,X76,X77,X78,X79,X80] : k5_enumset1(X75,X75,X76,X77,X78,X79,X80) = k4_enumset1(X75,X76,X77,X78,X79,X80) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_48,plain,(
    ! [X81,X82,X83,X84,X85,X86,X87] : k6_enumset1(X81,X81,X82,X83,X84,X85,X86,X87) = k5_enumset1(X81,X82,X83,X84,X85,X86,X87) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_58,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_59,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_40]),c_0_30])).

cnf(c_0_60,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_52]),c_0_28]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_56]),c_0_56]),c_0_56]),c_0_56]),c_0_56]),c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_57])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_62,plain,(
    ! [X51,X52,X53,X54,X55,X56,X57,X58,X59] : k7_enumset1(X51,X52,X53,X54,X55,X56,X57,X58,X59) = k2_xboole_0(k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58),k1_tarski(X59)) ),
    inference(variable_rename,[status(thm)],[t134_enumset1])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_49,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_40])).

cnf(c_0_67,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k3_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_51]),c_0_52]),c_0_28]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_56]),c_0_56]),c_0_57]),c_0_57])).

cnf(c_0_68,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_66]),c_0_30])).

cnf(c_0_69,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) = k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

fof(c_0_70,plain,(
    ! [X28,X29,X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40,X41,X42,X43,X44,X45,X46,X47,X48,X49] :
      ( ( ~ r2_hidden(X38,X37)
        | X38 = X28
        | X38 = X29
        | X38 = X30
        | X38 = X31
        | X38 = X32
        | X38 = X33
        | X38 = X34
        | X38 = X35
        | X38 = X36
        | X37 != k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( X39 != X28
        | r2_hidden(X39,X37)
        | X37 != k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( X39 != X29
        | r2_hidden(X39,X37)
        | X37 != k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( X39 != X30
        | r2_hidden(X39,X37)
        | X37 != k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( X39 != X31
        | r2_hidden(X39,X37)
        | X37 != k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( X39 != X32
        | r2_hidden(X39,X37)
        | X37 != k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( X39 != X33
        | r2_hidden(X39,X37)
        | X37 != k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( X39 != X34
        | r2_hidden(X39,X37)
        | X37 != k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( X39 != X35
        | r2_hidden(X39,X37)
        | X37 != k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( X39 != X36
        | r2_hidden(X39,X37)
        | X37 != k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36) )
      & ( esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) != X40
        | ~ r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | X49 = k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) != X41
        | ~ r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | X49 = k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) != X42
        | ~ r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | X49 = k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) != X43
        | ~ r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | X49 = k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) != X44
        | ~ r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | X49 = k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) != X45
        | ~ r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | X49 = k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) != X46
        | ~ r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | X49 = k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) != X47
        | ~ r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | X49 = k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) != X48
        | ~ r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | X49 = k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) )
      & ( r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)
        | esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) = X40
        | esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) = X41
        | esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) = X42
        | esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) = X43
        | esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) = X44
        | esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) = X45
        | esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) = X46
        | esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) = X47
        | esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49) = X48
        | X49 = k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_40])).

cnf(c_0_72,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_69])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X2,X4,X5,X6,X7,X8,X9,X10,X11) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_63])).

cnf(c_0_75,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_61])).

cnf(c_0_76,negated_conjecture,
    ( k3_xboole_0(k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_68]),c_0_72]),c_0_63]),c_0_61])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X2)
    | X2 != k7_enumset1(X1,X3,X4,X5,X6,X7,X8,X9,X10) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_78,plain,
    ( k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k7_enumset1(X1,X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_63])).

cnf(c_0_79,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_74]),c_0_30])).

cnf(c_0_80,negated_conjecture,
    ( k3_xboole_0(k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0),k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)) = k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_40]),c_0_30])).

cnf(c_0_81,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | X1 = X8
    | X1 = X9
    | X1 = X10
    | X1 = X11
    | ~ r2_hidden(X1,X2)
    | X2 != k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X10,X11) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0) = k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_84,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | X1 = X8
    | X1 = X9
    | X1 = X10
    | ~ r2_hidden(X1,k7_enumset1(X10,X9,X8,X7,X6,X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk3_0,k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.20/0.41  # and selection function SelectNegativeLiterals.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.028 s
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.41  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.41  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.20/0.41  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.20/0.41  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.20/0.41  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.20/0.41  fof(t13_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 0.20/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.41  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.41  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.41  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.41  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.41  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.41  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.41  fof(t134_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_enumset1)).
% 0.20/0.41  fof(d7_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9, X10]:(X10=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)<=>![X11]:(r2_hidden(X11,X10)<=>~(((((((((X11!=X1&X11!=X2)&X11!=X3)&X11!=X4)&X11!=X5)&X11!=X6)&X11!=X7)&X11!=X8)&X11!=X9)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_enumset1)).
% 0.20/0.41  fof(c_0_18, plain, ![X26, X27]:k2_xboole_0(X26,X27)=k5_xboole_0(X26,k4_xboole_0(X27,X26)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.41  fof(c_0_19, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.41  fof(c_0_20, plain, ![X21, X22]:r1_tarski(X21,k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.41  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  fof(c_0_23, plain, ![X23, X24, X25]:k5_xboole_0(k5_xboole_0(X23,X24),X25)=k5_xboole_0(X23,k5_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.20/0.41  fof(c_0_24, plain, ![X20]:k5_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.20/0.41  fof(c_0_25, plain, ![X18, X19]:k3_xboole_0(X18,k2_xboole_0(X18,X19))=X18, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.20/0.41  fof(c_0_26, plain, ![X14, X15]:((k4_xboole_0(X14,X15)!=k1_xboole_0|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|k4_xboole_0(X14,X15)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.20/0.41  cnf(c_0_27, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.41  cnf(c_0_29, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_30, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.41  cnf(c_0_31, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_33, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.41  cnf(c_0_34, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.41  cnf(c_0_35, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(rw,[status(thm)],[c_0_31, c_0_28])).
% 0.20/0.41  cnf(c_0_36, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_22])).
% 0.20/0.41  cnf(c_0_37, plain, (r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.41  cnf(c_0_38, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 0.20/0.41  fof(c_0_39, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t13_zfmisc_1])).
% 0.20/0.41  cnf(c_0_40, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.20/0.41  fof(c_0_41, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)&esk2_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 0.20/0.41  fof(c_0_42, plain, ![X60]:k2_tarski(X60,X60)=k1_tarski(X60), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.41  fof(c_0_43, plain, ![X61, X62]:k1_enumset1(X61,X61,X62)=k2_tarski(X61,X62), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.41  fof(c_0_44, plain, ![X63, X64, X65]:k2_enumset1(X63,X63,X64,X65)=k1_enumset1(X63,X64,X65), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.41  fof(c_0_45, plain, ![X66, X67, X68, X69]:k3_enumset1(X66,X66,X67,X68,X69)=k2_enumset1(X66,X67,X68,X69), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.41  fof(c_0_46, plain, ![X70, X71, X72, X73, X74]:k4_enumset1(X70,X70,X71,X72,X73,X74)=k3_enumset1(X70,X71,X72,X73,X74), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.41  fof(c_0_47, plain, ![X75, X76, X77, X78, X79, X80]:k5_enumset1(X75,X75,X76,X77,X78,X79,X80)=k4_enumset1(X75,X76,X77,X78,X79,X80), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.41  fof(c_0_48, plain, ![X81, X82, X83, X84, X85, X86, X87]:k6_enumset1(X81,X81,X82,X83,X84,X85,X86,X87)=k5_enumset1(X81,X82,X83,X84,X85,X86,X87), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.41  cnf(c_0_49, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_29, c_0_40])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.41  cnf(c_0_51, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.41  cnf(c_0_52, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.41  cnf(c_0_53, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.41  cnf(c_0_54, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.41  cnf(c_0_55, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.41  cnf(c_0_56, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.41  cnf(c_0_57, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.41  fof(c_0_58, plain, ![X12, X13]:k3_xboole_0(X12,X13)=k3_xboole_0(X13,X12), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.41  cnf(c_0_59, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_40]), c_0_30])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))))=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_52]), c_0_28]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_55]), c_0_55]), c_0_55]), c_0_55]), c_0_55]), c_0_56]), c_0_56]), c_0_56]), c_0_56]), c_0_56]), c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_57])).
% 0.20/0.41  cnf(c_0_61, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.41  fof(c_0_62, plain, ![X51, X52, X53, X54, X55, X56, X57, X58, X59]:k7_enumset1(X51,X52,X53,X54,X55,X56,X57,X58,X59)=k2_xboole_0(k6_enumset1(X51,X52,X53,X54,X55,X56,X57,X58),k1_tarski(X59)), inference(variable_rename,[status(thm)],[t134_enumset1])).
% 0.20/0.41  cnf(c_0_63, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_49, c_0_59])).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, (k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.41  cnf(c_0_65, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.41  cnf(c_0_66, negated_conjecture, (k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_40])).
% 0.20/0.41  cnf(c_0_67, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k3_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_51]), c_0_52]), c_0_28]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_55]), c_0_55]), c_0_56]), c_0_56]), c_0_57]), c_0_57])).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, (k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_66]), c_0_30])).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, (k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))=k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.41  fof(c_0_70, plain, ![X28, X29, X30, X31, X32, X33, X34, X35, X36, X37, X38, X39, X40, X41, X42, X43, X44, X45, X46, X47, X48, X49]:(((~r2_hidden(X38,X37)|(X38=X28|X38=X29|X38=X30|X38=X31|X38=X32|X38=X33|X38=X34|X38=X35|X38=X36)|X37!=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36))&(((((((((X39!=X28|r2_hidden(X39,X37)|X37!=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36))&(X39!=X29|r2_hidden(X39,X37)|X37!=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36)))&(X39!=X30|r2_hidden(X39,X37)|X37!=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36)))&(X39!=X31|r2_hidden(X39,X37)|X37!=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36)))&(X39!=X32|r2_hidden(X39,X37)|X37!=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36)))&(X39!=X33|r2_hidden(X39,X37)|X37!=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36)))&(X39!=X34|r2_hidden(X39,X37)|X37!=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36)))&(X39!=X35|r2_hidden(X39,X37)|X37!=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36)))&(X39!=X36|r2_hidden(X39,X37)|X37!=k7_enumset1(X28,X29,X30,X31,X32,X33,X34,X35,X36))))&((((((((((esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)!=X40|~r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)|X49=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48))&(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)!=X41|~r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)|X49=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48)))&(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)!=X42|~r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)|X49=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48)))&(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)!=X43|~r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)|X49=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48)))&(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)!=X44|~r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)|X49=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48)))&(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)!=X45|~r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)|X49=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48)))&(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)!=X46|~r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)|X49=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48)))&(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)!=X47|~r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)|X49=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48)))&(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)!=X48|~r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)|X49=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48)))&(r2_hidden(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49),X49)|(esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)=X40|esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)=X41|esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)=X42|esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)=X43|esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)=X44|esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)=X45|esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)=X46|esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)=X47|esk1_10(X40,X41,X42,X43,X44,X45,X46,X47,X48,X49)=X48)|X49=k7_enumset1(X40,X41,X42,X43,X44,X45,X46,X47,X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).
% 0.20/0.41  cnf(c_0_71, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_40])).
% 0.20/0.41  cnf(c_0_72, negated_conjecture, (k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))), inference(spm,[status(thm)],[c_0_63, c_0_69])).
% 0.20/0.41  cnf(c_0_73, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k7_enumset1(X2,X4,X5,X6,X7,X8,X9,X10,X11)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.41  cnf(c_0_74, negated_conjecture, (k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_63])).
% 0.20/0.41  cnf(c_0_75, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))=X1), inference(spm,[status(thm)],[c_0_35, c_0_61])).
% 0.20/0.41  cnf(c_0_76, negated_conjecture, (k3_xboole_0(k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_68]), c_0_72]), c_0_63]), c_0_61])).
% 0.20/0.41  cnf(c_0_77, plain, (r2_hidden(X1,X2)|X2!=k7_enumset1(X1,X3,X4,X5,X6,X7,X8,X9,X10)), inference(er,[status(thm)],[c_0_73])).
% 0.20/0.41  cnf(c_0_78, plain, (k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=k7_enumset1(X1,X1,X1,X1,X1,X1,X1,X1,X1)), inference(spm,[status(thm)],[c_0_67, c_0_63])).
% 0.20/0.41  cnf(c_0_79, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_74]), c_0_30])).
% 0.20/0.41  cnf(c_0_80, negated_conjecture, (k3_xboole_0(k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0),k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))=k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_40]), c_0_30])).
% 0.20/0.41  cnf(c_0_81, plain, (X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|X1=X8|X1=X9|X1=X10|X1=X11|~r2_hidden(X1,X2)|X2!=k7_enumset1(X3,X4,X5,X6,X7,X8,X9,X10,X11)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.41  cnf(c_0_82, plain, (r2_hidden(X1,k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9))), inference(er,[status(thm)],[c_0_77])).
% 0.20/0.41  cnf(c_0_83, negated_conjecture, (k7_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)=k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 0.20/0.41  cnf(c_0_84, plain, (X1=X2|X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|X1=X8|X1=X9|X1=X10|~r2_hidden(X1,k7_enumset1(X10,X9,X8,X7,X6,X5,X4,X3,X2))), inference(er,[status(thm)],[c_0_81])).
% 0.20/0.41  cnf(c_0_85, negated_conjecture, (r2_hidden(esk3_0,k7_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.20/0.41  cnf(c_0_86, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.41  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 88
% 0.20/0.41  # Proof object clause steps            : 51
% 0.20/0.41  # Proof object formula steps           : 37
% 0.20/0.41  # Proof object conjectures             : 18
% 0.20/0.41  # Proof object clause conjectures      : 15
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 20
% 0.20/0.41  # Proof object initial formulas used   : 18
% 0.20/0.41  # Proof object generating inferences   : 22
% 0.20/0.41  # Proof object simplifying inferences  : 65
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 18
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 39
% 0.20/0.41  # Removed in clause preprocessing      : 9
% 0.20/0.41  # Initial clauses in saturation        : 30
% 0.20/0.41  # Processed clauses                    : 518
% 0.20/0.41  # ...of these trivial                  : 95
% 0.20/0.41  # ...subsumed                          : 273
% 0.20/0.41  # ...remaining for further processing  : 150
% 0.20/0.41  # Other redundant clauses eliminated   : 9
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 0
% 0.20/0.41  # Backward-rewritten                   : 27
% 0.20/0.41  # Generated clauses                    : 2372
% 0.20/0.41  # ...of the previous two non-trivial   : 1547
% 0.20/0.41  # Contextual simplify-reflections      : 0
% 0.20/0.41  # Paramodulations                      : 2351
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 21
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 114
% 0.20/0.41  #    Positive orientable unit clauses  : 66
% 0.20/0.41  #    Positive unorientable unit clauses: 5
% 0.20/0.41  #    Negative unit clauses             : 1
% 0.20/0.41  #    Non-unit-clauses                  : 42
% 0.20/0.41  # Current number of unprocessed clauses: 1008
% 0.20/0.41  # ...number of literals in the above   : 1278
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 36
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 1268
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1151
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 166
% 0.20/0.41  # Unit Clause-clause subsumption calls : 47
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 304
% 0.20/0.41  # BW rewrite match successes           : 159
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 34347
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.060 s
% 0.20/0.41  # System time              : 0.007 s
% 0.20/0.41  # Total time               : 0.067 s
% 0.20/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
