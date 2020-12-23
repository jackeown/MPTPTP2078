%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:50 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  100 (1148 expanded)
%              Number of clauses        :   55 ( 426 expanded)
%              Number of leaves         :   22 ( 360 expanded)
%              Depth                    :   14
%              Number of atoms          :  125 (1176 expanded)
%              Number of equality atoms :   93 (1144 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t88_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t69_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
      | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t52_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

fof(c_0_22,plain,(
    ! [X58,X59] : k3_tarski(k2_tarski(X58,X59)) = k2_xboole_0(X58,X59) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X29,X30] : k1_enumset1(X29,X29,X30) = k2_tarski(X29,X30) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X24,X25] : k3_xboole_0(X24,X25) = k5_xboole_0(k5_xboole_0(X24,X25),k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_25,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X31,X32,X33] : k2_enumset1(X31,X31,X32,X33) = k1_enumset1(X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X34,X35,X36,X37] : k3_enumset1(X34,X34,X35,X36,X37) = k2_enumset1(X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X18,X19] :
      ( ~ r1_xboole_0(X18,X19)
      | k4_xboole_0(k2_xboole_0(X18,X19),X19) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).

fof(c_0_30,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X38,X39,X40,X41,X42] : k4_enumset1(X38,X38,X39,X40,X41,X42) = k3_enumset1(X38,X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_36,plain,(
    ! [X43,X44,X45,X46,X47,X48] : k5_enumset1(X43,X43,X44,X45,X46,X47,X48) = k4_enumset1(X43,X44,X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_37,plain,(
    ! [X49,X50,X51,X52,X53,X54,X55] : k6_enumset1(X49,X49,X50,X51,X52,X53,X54,X55) = k5_enumset1(X49,X50,X51,X52,X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_38,plain,(
    ! [X26,X27] : k2_tarski(X26,X27) = k2_tarski(X27,X26) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_39,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_40,plain,(
    ! [X20,X21,X22] : k5_xboole_0(k5_xboole_0(X20,X21),X22) = k5_xboole_0(X20,k5_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_44,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_50,plain,(
    ! [X23] : k5_xboole_0(X23,X23) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_51,plain,(
    ! [X17] : k5_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_52,plain,(
    ! [X56,X57] :
      ( r2_hidden(X56,X57)
      | r1_xboole_0(k1_tarski(X56),X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_53,plain,(
    ! [X28] : k2_tarski(X28,X28) = k1_tarski(X28) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_54,plain,(
    ! [X60] : k3_tarski(k1_tarski(X60)) = X60 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

fof(c_0_55,plain,(
    ! [X14,X15,X16] : k2_xboole_0(k2_xboole_0(X14,X15),X16) = k2_xboole_0(X14,k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_56,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
        | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    inference(assume_negation,[status(cth)],[t69_zfmisc_1])).

cnf(c_0_57,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2)))) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_32]),c_0_42]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46])).

cnf(c_0_58,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_26]),c_0_26]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_62,plain,(
    ! [X10,X11] :
      ( ~ r1_xboole_0(X10,X11)
      | r1_xboole_0(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_66,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_67,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk1_0),esk2_0) != k1_xboole_0
    & k4_xboole_0(k1_tarski(esk1_0),esk2_0) != k1_tarski(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_56])])])).

cnf(c_0_68,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k5_xboole_0(X2,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_48]),c_0_58]),c_0_49])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_70,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_26]),c_0_33]),c_0_34]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_72,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_64]),c_0_26]),c_0_33]),c_0_34]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_73,plain,
    ( k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46])).

cnf(c_0_74,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk1_0),esk2_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))) = X2
    | ~ r1_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_59]),c_0_49]),c_0_48]),c_0_69])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_77,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_72])).

fof(c_0_79,plain,(
    ! [X61,X62] :
      ( ~ r2_hidden(X61,X62)
      | k3_xboole_0(X62,k1_tarski(X61)) = k1_tarski(X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_zfmisc_1])])).

cnf(c_0_80,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0),k3_tarski(k6_enumset1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)))) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_64]),c_0_64]),c_0_26]),c_0_26]),c_0_42]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46])).

cnf(c_0_81,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))) = X2
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_58]),c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk1_0),esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_84,plain,
    ( k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))))) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_48]),c_0_58]),c_0_49])).

cnf(c_0_86,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0),k3_tarski(k6_enumset1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_64]),c_0_26]),c_0_42]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46])).

cnf(c_0_88,plain,
    ( k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_64]),c_0_64]),c_0_26]),c_0_26]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46])).

cnf(c_0_89,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_59]),c_0_49]),c_0_48]),c_0_69])).

cnf(c_0_90,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) = k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X1)
    | r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_tarski(k6_enumset1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0))))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_48]),c_0_49])).

cnf(c_0_92,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_88,c_0_49])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_48]),c_0_69])])).

cnf(c_0_94,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_91,c_0_58])).

cnf(c_0_95,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_96,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))))) = k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_59]),c_0_49]),c_0_48]),c_0_69])).

cnf(c_0_98,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_49]),c_0_48]),c_0_69])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98]),c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:56:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.46  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.19/0.46  # and selection function SelectNegativeLiterals.
% 0.19/0.46  #
% 0.19/0.46  # Preprocessing time       : 0.027 s
% 0.19/0.46  
% 0.19/0.46  # Proof found!
% 0.19/0.46  # SZS status Theorem
% 0.19/0.46  # SZS output start CNFRefutation
% 0.19/0.46  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.46  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.46  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.19/0.46  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.46  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.46  fof(t88_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 0.19/0.46  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.46  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.46  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.46  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.46  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.46  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.46  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.46  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.19/0.46  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.46  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.19/0.46  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.46  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.19/0.46  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.19/0.46  fof(t69_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 0.19/0.46  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.46  fof(t52_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 0.19/0.46  fof(c_0_22, plain, ![X58, X59]:k3_tarski(k2_tarski(X58,X59))=k2_xboole_0(X58,X59), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.46  fof(c_0_23, plain, ![X29, X30]:k1_enumset1(X29,X29,X30)=k2_tarski(X29,X30), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.46  fof(c_0_24, plain, ![X24, X25]:k3_xboole_0(X24,X25)=k5_xboole_0(k5_xboole_0(X24,X25),k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.19/0.46  cnf(c_0_25, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.46  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.46  fof(c_0_27, plain, ![X31, X32, X33]:k2_enumset1(X31,X31,X32,X33)=k1_enumset1(X31,X32,X33), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.46  fof(c_0_28, plain, ![X34, X35, X36, X37]:k3_enumset1(X34,X34,X35,X36,X37)=k2_enumset1(X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.46  fof(c_0_29, plain, ![X18, X19]:(~r1_xboole_0(X18,X19)|k4_xboole_0(k2_xboole_0(X18,X19),X19)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).
% 0.19/0.46  fof(c_0_30, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.46  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.46  cnf(c_0_32, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.46  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.46  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.46  fof(c_0_35, plain, ![X38, X39, X40, X41, X42]:k4_enumset1(X38,X38,X39,X40,X41,X42)=k3_enumset1(X38,X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.46  fof(c_0_36, plain, ![X43, X44, X45, X46, X47, X48]:k5_enumset1(X43,X43,X44,X45,X46,X47,X48)=k4_enumset1(X43,X44,X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.46  fof(c_0_37, plain, ![X49, X50, X51, X52, X53, X54, X55]:k6_enumset1(X49,X49,X50,X51,X52,X53,X54,X55)=k5_enumset1(X49,X50,X51,X52,X53,X54,X55), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.46  fof(c_0_38, plain, ![X26, X27]:k2_tarski(X26,X27)=k2_tarski(X27,X26), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.46  fof(c_0_39, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k5_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.46  fof(c_0_40, plain, ![X20, X21, X22]:k5_xboole_0(k5_xboole_0(X20,X21),X22)=k5_xboole_0(X20,k5_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.46  cnf(c_0_41, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.46  cnf(c_0_42, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.46  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])).
% 0.19/0.46  cnf(c_0_44, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.46  cnf(c_0_45, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.46  cnf(c_0_46, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.46  cnf(c_0_47, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.46  cnf(c_0_48, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.46  cnf(c_0_49, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.46  fof(c_0_50, plain, ![X23]:k5_xboole_0(X23,X23)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.19/0.46  fof(c_0_51, plain, ![X17]:k5_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.46  fof(c_0_52, plain, ![X56, X57]:(r2_hidden(X56,X57)|r1_xboole_0(k1_tarski(X56),X57)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.19/0.46  fof(c_0_53, plain, ![X28]:k2_tarski(X28,X28)=k1_tarski(X28), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.46  fof(c_0_54, plain, ![X60]:k3_tarski(k1_tarski(X60))=X60, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.19/0.46  fof(c_0_55, plain, ![X14, X15, X16]:k2_xboole_0(k2_xboole_0(X14,X15),X16)=k2_xboole_0(X14,k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.19/0.46  fof(c_0_56, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1))), inference(assume_negation,[status(cth)],[t69_zfmisc_1])).
% 0.19/0.46  cnf(c_0_57, plain, (k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2))))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_32]), c_0_42]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46])).
% 0.19/0.46  cnf(c_0_58, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_26]), c_0_26]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46])).
% 0.19/0.46  cnf(c_0_59, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.46  cnf(c_0_60, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.46  cnf(c_0_61, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.46  fof(c_0_62, plain, ![X10, X11]:(~r1_xboole_0(X10,X11)|r1_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.46  cnf(c_0_63, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.46  cnf(c_0_64, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.46  cnf(c_0_65, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.46  cnf(c_0_66, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.46  fof(c_0_67, negated_conjecture, (k4_xboole_0(k1_tarski(esk1_0),esk2_0)!=k1_xboole_0&k4_xboole_0(k1_tarski(esk1_0),esk2_0)!=k1_tarski(esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_56])])])).
% 0.19/0.46  cnf(c_0_68, plain, (k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k5_xboole_0(X2,k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_48]), c_0_58]), c_0_49])).
% 0.19/0.46  cnf(c_0_69, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.19/0.46  cnf(c_0_70, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.46  cnf(c_0_71, plain, (r2_hidden(X1,X2)|r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64]), c_0_26]), c_0_33]), c_0_34]), c_0_44]), c_0_45]), c_0_46])).
% 0.19/0.46  cnf(c_0_72, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_64]), c_0_26]), c_0_33]), c_0_34]), c_0_44]), c_0_45]), c_0_46])).
% 0.19/0.46  cnf(c_0_73, plain, (k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3))=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46])).
% 0.19/0.46  cnf(c_0_74, negated_conjecture, (k4_xboole_0(k1_tarski(esk1_0),esk2_0)!=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.46  cnf(c_0_75, plain, (k5_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))))=X2|~r1_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_59]), c_0_49]), c_0_48]), c_0_69])).
% 0.19/0.46  cnf(c_0_76, plain, (r2_hidden(X1,X2)|r1_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.46  cnf(c_0_77, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.46  cnf(c_0_78, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_73, c_0_72])).
% 0.19/0.46  fof(c_0_79, plain, ![X61, X62]:(~r2_hidden(X61,X62)|k3_xboole_0(X62,k1_tarski(X61))=k1_tarski(X61)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_zfmisc_1])])).
% 0.19/0.46  cnf(c_0_80, negated_conjecture, (k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0),k3_tarski(k6_enumset1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0))))!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_64]), c_0_64]), c_0_26]), c_0_26]), c_0_42]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46])).
% 0.19/0.46  cnf(c_0_81, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))))=X2|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.46  cnf(c_0_82, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))=k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_58]), c_0_78])).
% 0.19/0.46  cnf(c_0_83, negated_conjecture, (k4_xboole_0(k1_tarski(esk1_0),esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.46  cnf(c_0_84, plain, (k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.46  cnf(c_0_85, negated_conjecture, (k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))))))!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_48]), c_0_58]), c_0_49])).
% 0.19/0.46  cnf(c_0_86, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_81, c_0_82])).
% 0.19/0.46  cnf(c_0_87, negated_conjecture, (k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0),k3_tarski(k6_enumset1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0))))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_64]), c_0_26]), c_0_42]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46])).
% 0.19/0.46  cnf(c_0_88, plain, (k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_64]), c_0_64]), c_0_26]), c_0_26]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46])).
% 0.19/0.46  cnf(c_0_89, negated_conjecture, (k5_xboole_0(esk2_0,k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))))!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_59]), c_0_49]), c_0_48]), c_0_69])).
% 0.19/0.46  cnf(c_0_90, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))=k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X1)|r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_69, c_0_86])).
% 0.19/0.46  cnf(c_0_91, negated_conjecture, (k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_tarski(k6_enumset1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)))))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_48]), c_0_49])).
% 0.19/0.46  cnf(c_0_92, plain, (k5_xboole_0(X1,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_88, c_0_49])).
% 0.19/0.46  cnf(c_0_93, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_48]), c_0_69])])).
% 0.19/0.46  cnf(c_0_94, negated_conjecture, (k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))))))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_91, c_0_58])).
% 0.19/0.46  cnf(c_0_95, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.19/0.46  cnf(c_0_96, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))))=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.19/0.46  cnf(c_0_97, negated_conjecture, (k5_xboole_0(esk2_0,k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_59]), c_0_49]), c_0_48]), c_0_69])).
% 0.19/0.46  cnf(c_0_98, negated_conjecture, (k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_49]), c_0_48]), c_0_69])).
% 0.19/0.46  cnf(c_0_99, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_98]), c_0_60])]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 100
% 0.19/0.46  # Proof object clause steps            : 55
% 0.19/0.46  # Proof object formula steps           : 45
% 0.19/0.46  # Proof object conjectures             : 16
% 0.19/0.46  # Proof object clause conjectures      : 13
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 23
% 0.19/0.46  # Proof object initial formulas used   : 22
% 0.19/0.46  # Proof object generating inferences   : 12
% 0.19/0.46  # Proof object simplifying inferences  : 227
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 22
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 23
% 0.19/0.46  # Removed in clause preprocessing      : 10
% 0.19/0.46  # Initial clauses in saturation        : 13
% 0.19/0.46  # Processed clauses                    : 1244
% 0.19/0.46  # ...of these trivial                  : 815
% 0.19/0.46  # ...subsumed                          : 366
% 0.19/0.46  # ...remaining for further processing  : 63
% 0.19/0.46  # Other redundant clauses eliminated   : 0
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 0
% 0.19/0.46  # Backward-rewritten                   : 13
% 0.19/0.46  # Generated clauses                    : 3768
% 0.19/0.46  # ...of the previous two non-trivial   : 3349
% 0.19/0.46  # Contextual simplify-reflections      : 0
% 0.19/0.46  # Paramodulations                      : 3768
% 0.19/0.46  # Factorizations                       : 0
% 0.19/0.46  # Equation resolutions                 : 0
% 0.19/0.46  # Propositional unsat checks           : 0
% 0.19/0.46  #    Propositional check models        : 0
% 0.19/0.46  #    Propositional check unsatisfiable : 0
% 0.19/0.46  #    Propositional clauses             : 0
% 0.19/0.46  #    Propositional clauses after purity: 0
% 0.19/0.46  #    Propositional unsat core size     : 0
% 0.19/0.46  #    Propositional preprocessing time  : 0.000
% 0.19/0.46  #    Propositional encoding time       : 0.000
% 0.19/0.46  #    Propositional solver time         : 0.000
% 0.19/0.46  #    Success case prop preproc time    : 0.000
% 0.19/0.46  #    Success case prop encoding time   : 0.000
% 0.19/0.46  #    Success case prop solver time     : 0.000
% 0.19/0.46  # Current number of processed clauses  : 50
% 0.19/0.46  #    Positive orientable unit clauses  : 26
% 0.19/0.46  #    Positive unorientable unit clauses: 15
% 0.19/0.46  #    Negative unit clauses             : 0
% 0.19/0.46  #    Non-unit-clauses                  : 9
% 0.19/0.46  # Current number of unprocessed clauses: 1946
% 0.19/0.46  # ...number of literals in the above   : 2071
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 23
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 18
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 18
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 8
% 0.19/0.46  # Unit Clause-clause subsumption calls : 61
% 0.19/0.46  # Rewrite failures with RHS unbound    : 0
% 0.19/0.46  # BW rewrite match attempts            : 977
% 0.19/0.46  # BW rewrite match successes           : 220
% 0.19/0.46  # Condensation attempts                : 0
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 82960
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.119 s
% 0.19/0.46  # System time              : 0.006 s
% 0.19/0.46  # Total time               : 0.125 s
% 0.19/0.46  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
