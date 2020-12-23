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
% DateTime   : Thu Dec  3 10:37:01 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  106 (3570 expanded)
%              Number of clauses        :   59 (1315 expanded)
%              Number of leaves         :   23 (1121 expanded)
%              Depth                    :   19
%              Number of atoms          :  174 (3826 expanded)
%              Number of equality atoms :  131 (3507 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t6_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

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

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t118_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X4,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t113_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

fof(c_0_23,plain,(
    ! [X20,X21] : r1_xboole_0(k4_xboole_0(X20,X21),X21) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_24,plain,(
    ! [X13,X14] : k4_xboole_0(X13,X14) = k5_xboole_0(X13,k3_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_27,plain,(
    ! [X10] : k3_xboole_0(X10,X10) = X10 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t6_zfmisc_1])).

fof(c_0_29,plain,(
    ! [X11,X12] :
      ( ~ r1_xboole_0(X11,X12)
      | r1_xboole_0(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_30,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X22,X23] : k2_xboole_0(X22,X23) = k5_xboole_0(X22,k4_xboole_0(X23,X22)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_33,negated_conjecture,
    ( r1_tarski(k1_tarski(esk2_0),k1_tarski(esk3_0))
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

fof(c_0_34,plain,(
    ! [X54] : k2_tarski(X54,X54) = k1_tarski(X54) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_35,plain,(
    ! [X55,X56] : k1_enumset1(X55,X55,X56) = k2_tarski(X55,X56) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_36,plain,(
    ! [X57,X58,X59] : k2_enumset1(X57,X57,X58,X59) = k1_enumset1(X57,X58,X59) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_37,plain,(
    ! [X60,X61,X62,X63] : k3_enumset1(X60,X60,X61,X62,X63) = k2_enumset1(X60,X61,X62,X63) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_38,plain,(
    ! [X64,X65,X66,X67,X68] : k4_enumset1(X64,X64,X65,X66,X67,X68) = k3_enumset1(X64,X65,X66,X67,X68) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_39,plain,(
    ! [X69,X70,X71,X72,X73,X74] : k5_enumset1(X69,X69,X70,X71,X72,X73,X74) = k4_enumset1(X69,X70,X71,X72,X73,X74) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_40,plain,(
    ! [X75,X76,X77,X78,X79,X80,X81] : k6_enumset1(X75,X75,X76,X77,X78,X79,X80,X81) = k5_enumset1(X75,X76,X77,X78,X79,X80,X81) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_41,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_42,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_45,plain,(
    ! [X46,X47,X48,X49] : k2_enumset1(X46,X47,X48,X49) = k2_xboole_0(k1_tarski(X46),k1_enumset1(X47,X48,X49)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_47,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k1_tarski(esk2_0),k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_51,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_53,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_54,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_55,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_59,plain,(
    ! [X19] : k5_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_60,plain,(
    ! [X39,X40,X41,X42] : k2_enumset1(X39,X40,X41,X42) = k2_enumset1(X41,X42,X39,X40) ),
    inference(variable_rename,[status(thm)],[t118_enumset1])).

cnf(c_0_61,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_46,c_0_26])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_55]),c_0_55])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_26]),c_0_26])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X3,X4,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_69,plain,(
    ! [X50,X51,X52,X53] : k2_enumset1(X50,X51,X52,X53) = k2_xboole_0(k1_enumset1(X50,X51,X52),k1_tarski(X53)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_70,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_49]),c_0_50]),c_0_62]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_55])).

cnf(c_0_71,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_31])).

cnf(c_0_73,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X3,X3,X3,X3,X3,X4,X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_55]),c_0_55])).

cnf(c_0_74,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_67]),c_0_73])).

cnf(c_0_76,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_49]),c_0_50]),c_0_62]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_55])).

cnf(c_0_77,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk2_0)) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_75])).

fof(c_0_78,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X28,X27)
        | X28 = X24
        | X28 = X25
        | X28 = X26
        | X27 != k1_enumset1(X24,X25,X26) )
      & ( X29 != X24
        | r2_hidden(X29,X27)
        | X27 != k1_enumset1(X24,X25,X26) )
      & ( X29 != X25
        | r2_hidden(X29,X27)
        | X27 != k1_enumset1(X24,X25,X26) )
      & ( X29 != X26
        | r2_hidden(X29,X27)
        | X27 != k1_enumset1(X24,X25,X26) )
      & ( esk1_4(X30,X31,X32,X33) != X30
        | ~ r2_hidden(esk1_4(X30,X31,X32,X33),X33)
        | X33 = k1_enumset1(X30,X31,X32) )
      & ( esk1_4(X30,X31,X32,X33) != X31
        | ~ r2_hidden(esk1_4(X30,X31,X32,X33),X33)
        | X33 = k1_enumset1(X30,X31,X32) )
      & ( esk1_4(X30,X31,X32,X33) != X32
        | ~ r2_hidden(esk1_4(X30,X31,X32,X33),X33)
        | X33 = k1_enumset1(X30,X31,X32) )
      & ( r2_hidden(esk1_4(X30,X31,X32,X33),X33)
        | esk1_4(X30,X31,X32,X33) = X30
        | esk1_4(X30,X31,X32,X33) = X31
        | esk1_4(X30,X31,X32,X33) = X32
        | X33 = k1_enumset1(X30,X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_79,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk2_0) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_72]),c_0_67]),c_0_73])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_75,c_0_79])).

cnf(c_0_82,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_51]),c_0_52]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_84,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_81]),c_0_76])).

cnf(c_0_85,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_51]),c_0_52]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1,X2) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_84]),c_0_76])).

fof(c_0_88,plain,(
    ! [X43,X44,X45] : k1_enumset1(X43,X44,X45) = k2_xboole_0(k1_tarski(X43),k2_tarski(X44,X45)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

cnf(c_0_89,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X5 != k6_enumset1(X3,X3,X3,X3,X3,X2,X4,X4)
    | ~ r2_hidden(X1,X5) ),
    inference(spm,[status(thm)],[c_0_85,c_0_73])).

cnf(c_0_90,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk3_0) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_81,c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X3,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_92,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

fof(c_0_93,plain,(
    ! [X35,X36,X37,X38] : k2_enumset1(X35,X36,X37,X38) = k2_enumset1(X36,X38,X37,X35) ),
    inference(variable_rename,[status(thm)],[t113_enumset1])).

cnf(c_0_94,negated_conjecture,
    ( X1 = esk3_0
    | X2 != k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_84]),c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X2,X1)) ),
    inference(er,[status(thm)],[c_0_91])).

cnf(c_0_96,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_49]),c_0_50]),c_0_50]),c_0_62]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_55]),c_0_55]),c_0_55])).

cnf(c_0_97,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( X1 = esk3_0
    | k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X2,X1) != k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) ),
    inference(rw,[status(thm)],[c_0_96,c_0_70])).

cnf(c_0_100,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X2,X2,X2,X2,X2,X4,X3,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_55]),c_0_55])).

cnf(c_0_101,negated_conjecture,
    ( X1 = esk3_0
    | k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1) != k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_102,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X3,X3,X3,X3,X3,X2,X4,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_100])).

cnf(c_0_103,negated_conjecture,
    ( X1 = esk3_0
    | k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1,esk2_0,esk3_0) != k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_100]),c_0_102])).

cnf(c_0_104,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_103]),c_0_104]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:15:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.38/0.55  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.38/0.55  # and selection function SelectNegativeLiterals.
% 0.38/0.55  #
% 0.38/0.55  # Preprocessing time       : 0.028 s
% 0.38/0.55  
% 0.38/0.55  # Proof found!
% 0.38/0.55  # SZS status Theorem
% 0.38/0.55  # SZS output start CNFRefutation
% 0.38/0.55  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.38/0.55  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.38/0.55  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.38/0.55  fof(t6_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 0.38/0.55  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.38/0.55  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.38/0.55  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.38/0.55  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.38/0.55  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.38/0.55  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.38/0.55  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.38/0.55  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.38/0.55  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.38/0.55  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.38/0.55  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.38/0.55  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.38/0.55  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.38/0.55  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.38/0.55  fof(t118_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X4,X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_enumset1)).
% 0.38/0.55  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 0.38/0.55  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.38/0.55  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.38/0.55  fof(t113_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X3,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 0.38/0.55  fof(c_0_23, plain, ![X20, X21]:r1_xboole_0(k4_xboole_0(X20,X21),X21), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.38/0.55  fof(c_0_24, plain, ![X13, X14]:k4_xboole_0(X13,X14)=k5_xboole_0(X13,k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.38/0.55  cnf(c_0_25, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.38/0.55  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.38/0.55  fof(c_0_27, plain, ![X10]:k3_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.38/0.55  fof(c_0_28, negated_conjecture, ~(![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2)), inference(assume_negation,[status(cth)],[t6_zfmisc_1])).
% 0.38/0.55  fof(c_0_29, plain, ![X11, X12]:(~r1_xboole_0(X11,X12)|r1_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.38/0.55  cnf(c_0_30, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.38/0.55  cnf(c_0_31, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.38/0.55  fof(c_0_32, plain, ![X22, X23]:k2_xboole_0(X22,X23)=k5_xboole_0(X22,k4_xboole_0(X23,X22)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.38/0.55  fof(c_0_33, negated_conjecture, (r1_tarski(k1_tarski(esk2_0),k1_tarski(esk3_0))&esk2_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.38/0.55  fof(c_0_34, plain, ![X54]:k2_tarski(X54,X54)=k1_tarski(X54), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.38/0.55  fof(c_0_35, plain, ![X55, X56]:k1_enumset1(X55,X55,X56)=k2_tarski(X55,X56), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.38/0.55  fof(c_0_36, plain, ![X57, X58, X59]:k2_enumset1(X57,X57,X58,X59)=k1_enumset1(X57,X58,X59), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.38/0.55  fof(c_0_37, plain, ![X60, X61, X62, X63]:k3_enumset1(X60,X60,X61,X62,X63)=k2_enumset1(X60,X61,X62,X63), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.38/0.55  fof(c_0_38, plain, ![X64, X65, X66, X67, X68]:k4_enumset1(X64,X64,X65,X66,X67,X68)=k3_enumset1(X64,X65,X66,X67,X68), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.38/0.55  fof(c_0_39, plain, ![X69, X70, X71, X72, X73, X74]:k5_enumset1(X69,X69,X70,X71,X72,X73,X74)=k4_enumset1(X69,X70,X71,X72,X73,X74), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.38/0.55  fof(c_0_40, plain, ![X75, X76, X77, X78, X79, X80, X81]:k6_enumset1(X75,X75,X76,X77,X78,X79,X80,X81)=k5_enumset1(X75,X76,X77,X78,X79,X80,X81), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.38/0.55  fof(c_0_41, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.38/0.55  fof(c_0_42, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.38/0.55  cnf(c_0_43, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.38/0.55  cnf(c_0_44, plain, (r1_xboole_0(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.38/0.55  fof(c_0_45, plain, ![X46, X47, X48, X49]:k2_enumset1(X46,X47,X48,X49)=k2_xboole_0(k1_tarski(X46),k1_enumset1(X47,X48,X49)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.38/0.55  cnf(c_0_46, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.38/0.55  fof(c_0_47, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.38/0.55  cnf(c_0_48, negated_conjecture, (r1_tarski(k1_tarski(esk2_0),k1_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.38/0.55  cnf(c_0_49, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.38/0.55  cnf(c_0_50, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.38/0.55  cnf(c_0_51, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.38/0.55  cnf(c_0_52, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.38/0.55  cnf(c_0_53, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.38/0.55  cnf(c_0_54, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.38/0.55  cnf(c_0_55, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.38/0.55  cnf(c_0_56, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.38/0.55  cnf(c_0_57, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.38/0.55  cnf(c_0_58, plain, (r1_xboole_0(X1,k5_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.38/0.55  fof(c_0_59, plain, ![X19]:k5_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.38/0.55  fof(c_0_60, plain, ![X39, X40, X41, X42]:k2_enumset1(X39,X40,X41,X42)=k2_enumset1(X41,X42,X39,X40), inference(variable_rename,[status(thm)],[t118_enumset1])).
% 0.38/0.55  cnf(c_0_61, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.38/0.55  cnf(c_0_62, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_46, c_0_26])).
% 0.38/0.55  cnf(c_0_63, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.38/0.55  cnf(c_0_64, negated_conjecture, (r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_55]), c_0_55])).
% 0.38/0.55  cnf(c_0_65, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_26]), c_0_26])).
% 0.38/0.55  cnf(c_0_66, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.38/0.55  cnf(c_0_67, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.38/0.55  cnf(c_0_68, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X3,X4,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.38/0.55  fof(c_0_69, plain, ![X50, X51, X52, X53]:k2_enumset1(X50,X51,X52,X53)=k2_xboole_0(k1_enumset1(X50,X51,X52),k1_tarski(X53)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.38/0.55  cnf(c_0_70, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_49]), c_0_50]), c_0_62]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_55]), c_0_55]), c_0_55]), c_0_55]), c_0_55])).
% 0.38/0.55  cnf(c_0_71, negated_conjecture, (k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.38/0.55  cnf(c_0_72, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_31])).
% 0.38/0.55  cnf(c_0_73, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X3,X3,X3,X3,X3,X4,X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_55]), c_0_55])).
% 0.38/0.55  cnf(c_0_74, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.38/0.55  cnf(c_0_75, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_67]), c_0_73])).
% 0.38/0.55  cnf(c_0_76, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_49]), c_0_50]), c_0_62]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_55]), c_0_55]), c_0_55]), c_0_55]), c_0_55])).
% 0.38/0.55  cnf(c_0_77, negated_conjecture, (k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk2_0))=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_71, c_0_75])).
% 0.38/0.55  fof(c_0_78, plain, ![X24, X25, X26, X27, X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X28,X27)|(X28=X24|X28=X25|X28=X26)|X27!=k1_enumset1(X24,X25,X26))&(((X29!=X24|r2_hidden(X29,X27)|X27!=k1_enumset1(X24,X25,X26))&(X29!=X25|r2_hidden(X29,X27)|X27!=k1_enumset1(X24,X25,X26)))&(X29!=X26|r2_hidden(X29,X27)|X27!=k1_enumset1(X24,X25,X26))))&((((esk1_4(X30,X31,X32,X33)!=X30|~r2_hidden(esk1_4(X30,X31,X32,X33),X33)|X33=k1_enumset1(X30,X31,X32))&(esk1_4(X30,X31,X32,X33)!=X31|~r2_hidden(esk1_4(X30,X31,X32,X33),X33)|X33=k1_enumset1(X30,X31,X32)))&(esk1_4(X30,X31,X32,X33)!=X32|~r2_hidden(esk1_4(X30,X31,X32,X33),X33)|X33=k1_enumset1(X30,X31,X32)))&(r2_hidden(esk1_4(X30,X31,X32,X33),X33)|(esk1_4(X30,X31,X32,X33)=X30|esk1_4(X30,X31,X32,X33)=X31|esk1_4(X30,X31,X32,X33)=X32)|X33=k1_enumset1(X30,X31,X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.38/0.55  cnf(c_0_79, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk2_0)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_72]), c_0_67]), c_0_73])).
% 0.38/0.55  cnf(c_0_80, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.38/0.55  cnf(c_0_81, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_75, c_0_79])).
% 0.38/0.55  cnf(c_0_82, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.38/0.55  cnf(c_0_83, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_51]), c_0_52]), c_0_53]), c_0_54]), c_0_55])).
% 0.38/0.55  cnf(c_0_84, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_81]), c_0_76])).
% 0.38/0.55  cnf(c_0_85, plain, (X1=X5|X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_51]), c_0_52]), c_0_53]), c_0_54]), c_0_55])).
% 0.38/0.55  cnf(c_0_86, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_83])).
% 0.38/0.55  cnf(c_0_87, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1,X2)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_84]), c_0_76])).
% 0.38/0.55  fof(c_0_88, plain, ![X43, X44, X45]:k1_enumset1(X43,X44,X45)=k2_xboole_0(k1_tarski(X43),k2_tarski(X44,X45)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.38/0.55  cnf(c_0_89, plain, (X1=X2|X1=X3|X1=X4|X5!=k6_enumset1(X3,X3,X3,X3,X3,X2,X4,X4)|~r2_hidden(X1,X5)), inference(spm,[status(thm)],[c_0_85, c_0_73])).
% 0.38/0.55  cnf(c_0_90, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,esk3_0)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_81, c_0_84])).
% 0.38/0.55  cnf(c_0_91, negated_conjecture, (r2_hidden(X1,X2)|X2!=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X3,X1)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.38/0.55  cnf(c_0_92, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.38/0.55  fof(c_0_93, plain, ![X35, X36, X37, X38]:k2_enumset1(X35,X36,X37,X38)=k2_enumset1(X36,X38,X37,X35), inference(variable_rename,[status(thm)],[t113_enumset1])).
% 0.38/0.55  cnf(c_0_94, negated_conjecture, (X1=esk3_0|X2!=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_84]), c_0_90])).
% 0.38/0.55  cnf(c_0_95, negated_conjecture, (r2_hidden(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X2,X1))), inference(er,[status(thm)],[c_0_91])).
% 0.38/0.55  cnf(c_0_96, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_49]), c_0_50]), c_0_50]), c_0_62]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_55]), c_0_55]), c_0_55]), c_0_55]), c_0_55])).
% 0.38/0.55  cnf(c_0_97, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.38/0.55  cnf(c_0_98, negated_conjecture, (X1=esk3_0|k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X2,X1)!=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.38/0.55  cnf(c_0_99, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X2,X3)=k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)), inference(rw,[status(thm)],[c_0_96, c_0_70])).
% 0.38/0.55  cnf(c_0_100, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X2,X2,X2,X2,X2,X4,X3,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_55]), c_0_55])).
% 0.38/0.55  cnf(c_0_101, negated_conjecture, (X1=esk3_0|k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,X1)!=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.38/0.55  cnf(c_0_102, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X3,X3,X3,X3,X3,X2,X4,X1)), inference(spm,[status(thm)],[c_0_73, c_0_100])).
% 0.38/0.55  cnf(c_0_103, negated_conjecture, (X1=esk3_0|k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1,esk2_0,esk3_0)!=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_100]), c_0_102])).
% 0.38/0.55  cnf(c_0_104, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.38/0.55  cnf(c_0_105, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_103]), c_0_104]), ['proof']).
% 0.38/0.55  # SZS output end CNFRefutation
% 0.38/0.55  # Proof object total steps             : 106
% 0.38/0.55  # Proof object clause steps            : 59
% 0.38/0.55  # Proof object formula steps           : 47
% 0.38/0.55  # Proof object conjectures             : 21
% 0.38/0.55  # Proof object clause conjectures      : 18
% 0.38/0.55  # Proof object formula conjectures     : 3
% 0.38/0.55  # Proof object initial clauses used    : 25
% 0.38/0.55  # Proof object initial formulas used   : 23
% 0.38/0.55  # Proof object generating inferences   : 18
% 0.38/0.55  # Proof object simplifying inferences  : 145
% 0.38/0.55  # Training examples: 0 positive, 0 negative
% 0.38/0.55  # Parsed axioms                        : 23
% 0.38/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.55  # Initial clauses                      : 32
% 0.38/0.55  # Removed in clause preprocessing      : 9
% 0.38/0.55  # Initial clauses in saturation        : 23
% 0.38/0.55  # Processed clauses                    : 533
% 0.38/0.55  # ...of these trivial                  : 16
% 0.38/0.55  # ...subsumed                          : 398
% 0.38/0.55  # ...remaining for further processing  : 119
% 0.38/0.55  # Other redundant clauses eliminated   : 344
% 0.38/0.55  # Clauses deleted for lack of memory   : 0
% 0.38/0.55  # Backward-subsumed                    : 0
% 0.38/0.55  # Backward-rewritten                   : 19
% 0.38/0.55  # Generated clauses                    : 5200
% 0.38/0.55  # ...of the previous two non-trivial   : 4525
% 0.38/0.55  # Contextual simplify-reflections      : 0
% 0.38/0.55  # Paramodulations                      : 4796
% 0.38/0.55  # Factorizations                       : 28
% 0.38/0.55  # Equation resolutions                 : 376
% 0.38/0.55  # Propositional unsat checks           : 0
% 0.38/0.55  #    Propositional check models        : 0
% 0.38/0.55  #    Propositional check unsatisfiable : 0
% 0.38/0.55  #    Propositional clauses             : 0
% 0.38/0.55  #    Propositional clauses after purity: 0
% 0.38/0.55  #    Propositional unsat core size     : 0
% 0.38/0.55  #    Propositional preprocessing time  : 0.000
% 0.38/0.55  #    Propositional encoding time       : 0.000
% 0.38/0.55  #    Propositional solver time         : 0.000
% 0.38/0.55  #    Success case prop preproc time    : 0.000
% 0.38/0.55  #    Success case prop encoding time   : 0.000
% 0.38/0.55  #    Success case prop solver time     : 0.000
% 0.38/0.55  # Current number of processed clauses  : 97
% 0.38/0.55  #    Positive orientable unit clauses  : 31
% 0.38/0.55  #    Positive unorientable unit clauses: 5
% 0.38/0.55  #    Negative unit clauses             : 1
% 0.38/0.55  #    Non-unit-clauses                  : 60
% 0.38/0.55  # Current number of unprocessed clauses: 3992
% 0.38/0.55  # ...number of literals in the above   : 31649
% 0.38/0.55  # Current number of archived formulas  : 0
% 0.38/0.55  # Current number of archived clauses   : 28
% 0.38/0.55  # Clause-clause subsumption calls (NU) : 4339
% 0.38/0.55  # Rec. Clause-clause subsumption calls : 2919
% 0.38/0.55  # Non-unit clause-clause subsumptions  : 394
% 0.38/0.55  # Unit Clause-clause subsumption calls : 31
% 0.38/0.55  # Rewrite failures with RHS unbound    : 0
% 0.38/0.55  # BW rewrite match attempts            : 245
% 0.38/0.55  # BW rewrite match successes           : 171
% 0.38/0.55  # Condensation attempts                : 0
% 0.38/0.55  # Condensation successes               : 0
% 0.38/0.55  # Termbank termtop insertions          : 104589
% 0.38/0.55  
% 0.38/0.55  # -------------------------------------------------
% 0.38/0.55  # User time                : 0.201 s
% 0.38/0.55  # System time              : 0.003 s
% 0.38/0.55  # Total time               : 0.204 s
% 0.38/0.55  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
