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
% DateTime   : Thu Dec  3 10:42:32 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 506 expanded)
%              Number of clauses        :   44 ( 204 expanded)
%              Number of leaves         :   21 ( 149 expanded)
%              Depth                    :   15
%              Number of atoms          :  132 ( 569 expanded)
%              Number of equality atoms :   76 ( 508 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    7 (   2 average)

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

fof(t66_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ~ ( k4_xboole_0(X1,k1_tarski(X2)) = k1_xboole_0
        & X1 != k1_xboole_0
        & X1 != k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(c_0_21,plain,(
    ! [X51,X52] : k3_tarski(k2_tarski(X51,X52)) = k2_xboole_0(X51,X52) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X27,X28] : k1_enumset1(X27,X27,X28) = k2_tarski(X27,X28) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X24,X25] : k3_xboole_0(X24,X25) = k5_xboole_0(k5_xboole_0(X24,X25),k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_24,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X29,X30,X31] : k2_enumset1(X29,X29,X30,X31) = k1_enumset1(X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X32,X33,X34,X35] : k3_enumset1(X32,X32,X33,X34,X35) = k2_enumset1(X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( k4_xboole_0(X1,k1_tarski(X2)) = k1_xboole_0
          & X1 != k1_xboole_0
          & X1 != k1_tarski(X2) ) ),
    inference(assume_negation,[status(cth)],[t66_zfmisc_1])).

fof(c_0_29,plain,(
    ! [X8] : k3_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X36,X37,X38,X39,X40] : k4_enumset1(X36,X36,X37,X38,X39,X40) = k3_enumset1(X36,X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_35,plain,(
    ! [X41,X42,X43,X44,X45,X46] : k5_enumset1(X41,X41,X42,X43,X44,X45,X46) = k4_enumset1(X41,X42,X43,X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_36,plain,(
    ! [X7] : k2_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_37,negated_conjecture,
    ( k4_xboole_0(esk1_0,k1_tarski(esk2_0)) = k1_xboole_0
    & esk1_0 != k1_xboole_0
    & esk1_0 != k1_tarski(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

fof(c_0_38,plain,(
    ! [X26] : k2_tarski(X26,X26) = k1_tarski(X26) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_39,plain,(
    ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_42,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,plain,(
    ! [X23] : k5_xboole_0(X23,X23) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk1_0,k1_tarski(esk2_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_49,plain,(
    ! [X20,X21,X22] : k5_xboole_0(k5_xboole_0(X20,X21),X22) = k5_xboole_0(X20,k5_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_31]),c_0_32]),c_0_33]),c_0_42]),c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k5_xboole_0(esk1_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k3_tarski(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_25]),c_0_48]),c_0_32]),c_0_33]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

fof(c_0_56,plain,(
    ! [X49,X50] :
      ( r2_hidden(X49,X50)
      | r1_xboole_0(k1_tarski(X49),X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_57,plain,(
    ! [X18,X19] : r1_tarski(X18,k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_tarski(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_51]),c_0_55])).

fof(c_0_60,plain,(
    ! [X13] : k5_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_61,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_xboole_0(X15,X16)
      | r1_xboole_0(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_tarski(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_66,plain,(
    ! [X47,X48] :
      ( ( ~ r1_tarski(k1_tarski(X47),X48)
        | r2_hidden(X47,X48) )
      & ( ~ r2_hidden(X47,X48)
        | r1_tarski(k1_tarski(X47),X48) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_67,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_47]),c_0_25]),c_0_32]),c_0_33]),c_0_42]),c_0_43])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_31]),c_0_32]),c_0_33]),c_0_42]),c_0_43])).

cnf(c_0_70,negated_conjecture,
    ( k3_tarski(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) = k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_64]),c_0_65])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(X3,X2)
    | ~ r1_tarski(X3,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(esk1_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

fof(c_0_74,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_75,plain,
    ( r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_47]),c_0_25]),c_0_32]),c_0_33]),c_0_42]),c_0_43])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk2_0,X1)
    | r1_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_77,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(esk1_0,X1)
    | r1_tarski(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( esk1_0 != k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_80,plain,(
    ! [X17] :
      ( ( r1_xboole_0(X17,X17)
        | X17 != k1_xboole_0 )
      & ( X17 = k1_xboole_0
        | ~ r1_xboole_0(X17,X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_81,negated_conjecture,
    ( k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = X1
    | r1_xboole_0(esk1_0,X1)
    | ~ r1_tarski(X1,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( esk1_0 != k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_47]),c_0_25]),c_0_32]),c_0_33]),c_0_42]),c_0_43])).

cnf(c_0_83,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_73]),c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n014.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:52:37 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.16/0.35  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.16/0.35  # and selection function SelectNegativeLiterals.
% 0.16/0.35  #
% 0.16/0.35  # Preprocessing time       : 0.027 s
% 0.16/0.35  
% 0.16/0.35  # Proof found!
% 0.16/0.35  # SZS status Theorem
% 0.16/0.35  # SZS output start CNFRefutation
% 0.16/0.35  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.16/0.35  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.16/0.35  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.16/0.35  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.16/0.35  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.16/0.35  fof(t66_zfmisc_1, conjecture, ![X1, X2]:~(((k4_xboole_0(X1,k1_tarski(X2))=k1_xboole_0&X1!=k1_xboole_0)&X1!=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 0.16/0.35  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.16/0.35  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.16/0.35  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.16/0.35  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.16/0.35  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.16/0.35  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.16/0.35  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.16/0.35  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.16/0.35  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.16/0.35  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.16/0.35  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.16/0.35  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.16/0.35  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.16/0.35  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.16/0.35  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.16/0.35  fof(c_0_21, plain, ![X51, X52]:k3_tarski(k2_tarski(X51,X52))=k2_xboole_0(X51,X52), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.16/0.35  fof(c_0_22, plain, ![X27, X28]:k1_enumset1(X27,X27,X28)=k2_tarski(X27,X28), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.16/0.35  fof(c_0_23, plain, ![X24, X25]:k3_xboole_0(X24,X25)=k5_xboole_0(k5_xboole_0(X24,X25),k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.16/0.35  cnf(c_0_24, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.16/0.35  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.16/0.35  fof(c_0_26, plain, ![X29, X30, X31]:k2_enumset1(X29,X29,X30,X31)=k1_enumset1(X29,X30,X31), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.16/0.35  fof(c_0_27, plain, ![X32, X33, X34, X35]:k3_enumset1(X32,X32,X33,X34,X35)=k2_enumset1(X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.16/0.35  fof(c_0_28, negated_conjecture, ~(![X1, X2]:~(((k4_xboole_0(X1,k1_tarski(X2))=k1_xboole_0&X1!=k1_xboole_0)&X1!=k1_tarski(X2)))), inference(assume_negation,[status(cth)],[t66_zfmisc_1])).
% 0.16/0.35  fof(c_0_29, plain, ![X8]:k3_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.16/0.35  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.16/0.35  cnf(c_0_31, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.16/0.35  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.16/0.35  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.16/0.35  fof(c_0_34, plain, ![X36, X37, X38, X39, X40]:k4_enumset1(X36,X36,X37,X38,X39,X40)=k3_enumset1(X36,X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.16/0.35  fof(c_0_35, plain, ![X41, X42, X43, X44, X45, X46]:k5_enumset1(X41,X41,X42,X43,X44,X45,X46)=k4_enumset1(X41,X42,X43,X44,X45,X46), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.16/0.35  fof(c_0_36, plain, ![X7]:k2_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.16/0.35  fof(c_0_37, negated_conjecture, ((k4_xboole_0(esk1_0,k1_tarski(esk2_0))=k1_xboole_0&esk1_0!=k1_xboole_0)&esk1_0!=k1_tarski(esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.16/0.35  fof(c_0_38, plain, ![X26]:k2_tarski(X26,X26)=k1_tarski(X26), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.16/0.35  fof(c_0_39, plain, ![X11, X12]:k4_xboole_0(X11,X12)=k5_xboole_0(X11,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.16/0.35  cnf(c_0_40, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.16/0.35  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])).
% 0.16/0.35  cnf(c_0_42, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.16/0.35  cnf(c_0_43, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.16/0.35  fof(c_0_44, plain, ![X23]:k5_xboole_0(X23,X23)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.16/0.35  cnf(c_0_45, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.16/0.35  cnf(c_0_46, negated_conjecture, (k4_xboole_0(esk1_0,k1_tarski(esk2_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.16/0.35  cnf(c_0_47, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.16/0.35  cnf(c_0_48, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.16/0.35  fof(c_0_49, plain, ![X20, X21, X22]:k5_xboole_0(k5_xboole_0(X20,X21),X22)=k5_xboole_0(X20,k5_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.16/0.35  cnf(c_0_50, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43])).
% 0.16/0.35  cnf(c_0_51, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.16/0.35  cnf(c_0_52, plain, (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_31]), c_0_32]), c_0_33]), c_0_42]), c_0_43])).
% 0.16/0.35  cnf(c_0_53, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k5_xboole_0(esk1_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k3_tarski(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_25]), c_0_48]), c_0_32]), c_0_33]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43])).
% 0.16/0.35  cnf(c_0_54, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.16/0.35  cnf(c_0_55, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.16/0.35  fof(c_0_56, plain, ![X49, X50]:(r2_hidden(X49,X50)|r1_xboole_0(k1_tarski(X49),X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.16/0.35  fof(c_0_57, plain, ![X18, X19]:r1_tarski(X18,k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.16/0.35  cnf(c_0_58, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_tarski(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.16/0.35  cnf(c_0_59, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_51]), c_0_55])).
% 0.16/0.35  fof(c_0_60, plain, ![X13]:k5_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.16/0.35  fof(c_0_61, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|~r1_xboole_0(X15,X16)|r1_xboole_0(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.16/0.35  cnf(c_0_62, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.16/0.35  cnf(c_0_63, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.16/0.35  cnf(c_0_64, negated_conjecture, (k5_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_tarski(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.16/0.35  cnf(c_0_65, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.16/0.35  fof(c_0_66, plain, ![X47, X48]:((~r1_tarski(k1_tarski(X47),X48)|r2_hidden(X47,X48))&(~r2_hidden(X47,X48)|r1_tarski(k1_tarski(X47),X48))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.16/0.35  cnf(c_0_67, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.16/0.35  cnf(c_0_68, plain, (r2_hidden(X1,X2)|r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_47]), c_0_25]), c_0_32]), c_0_33]), c_0_42]), c_0_43])).
% 0.16/0.35  cnf(c_0_69, plain, (r1_tarski(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_31]), c_0_32]), c_0_33]), c_0_42]), c_0_43])).
% 0.16/0.35  cnf(c_0_70, negated_conjecture, (k3_tarski(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))=k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_64]), c_0_65])).
% 0.16/0.35  cnf(c_0_71, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.16/0.35  cnf(c_0_72, plain, (r2_hidden(X1,X2)|r1_xboole_0(X3,X2)|~r1_tarski(X3,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.16/0.35  cnf(c_0_73, negated_conjecture, (r1_tarski(esk1_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.16/0.35  fof(c_0_74, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.16/0.35  cnf(c_0_75, plain, (r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_47]), c_0_25]), c_0_32]), c_0_33]), c_0_42]), c_0_43])).
% 0.16/0.35  cnf(c_0_76, negated_conjecture, (r2_hidden(esk2_0,X1)|r1_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.16/0.35  cnf(c_0_77, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.16/0.35  cnf(c_0_78, negated_conjecture, (r1_xboole_0(esk1_0,X1)|r1_tarski(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.16/0.35  cnf(c_0_79, negated_conjecture, (esk1_0!=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.16/0.35  fof(c_0_80, plain, ![X17]:((r1_xboole_0(X17,X17)|X17!=k1_xboole_0)&(X17=k1_xboole_0|~r1_xboole_0(X17,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.16/0.35  cnf(c_0_81, negated_conjecture, (k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=X1|r1_xboole_0(esk1_0,X1)|~r1_tarski(X1,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.16/0.35  cnf(c_0_82, negated_conjecture, (esk1_0!=k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_47]), c_0_25]), c_0_32]), c_0_33]), c_0_42]), c_0_43])).
% 0.16/0.35  cnf(c_0_83, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.16/0.35  cnf(c_0_84, negated_conjecture, (r1_xboole_0(esk1_0,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_73]), c_0_82])).
% 0.16/0.35  cnf(c_0_85, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.16/0.35  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85]), ['proof']).
% 0.16/0.35  # SZS output end CNFRefutation
% 0.16/0.35  # Proof object total steps             : 87
% 0.16/0.35  # Proof object clause steps            : 44
% 0.16/0.35  # Proof object formula steps           : 43
% 0.16/0.35  # Proof object conjectures             : 17
% 0.16/0.35  # Proof object clause conjectures      : 14
% 0.16/0.35  # Proof object formula conjectures     : 3
% 0.16/0.35  # Proof object initial clauses used    : 23
% 0.16/0.35  # Proof object initial formulas used   : 21
% 0.16/0.35  # Proof object generating inferences   : 9
% 0.16/0.35  # Proof object simplifying inferences  : 55
% 0.16/0.35  # Training examples: 0 positive, 0 negative
% 0.16/0.35  # Parsed axioms                        : 21
% 0.16/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.35  # Initial clauses                      : 27
% 0.16/0.35  # Removed in clause preprocessing      : 9
% 0.16/0.35  # Initial clauses in saturation        : 18
% 0.16/0.35  # Processed clauses                    : 91
% 0.16/0.35  # ...of these trivial                  : 9
% 0.16/0.35  # ...subsumed                          : 34
% 0.16/0.35  # ...remaining for further processing  : 48
% 0.16/0.35  # Other redundant clauses eliminated   : 2
% 0.16/0.35  # Clauses deleted for lack of memory   : 0
% 0.16/0.35  # Backward-subsumed                    : 1
% 0.16/0.35  # Backward-rewritten                   : 6
% 0.16/0.35  # Generated clauses                    : 273
% 0.16/0.35  # ...of the previous two non-trivial   : 162
% 0.16/0.35  # Contextual simplify-reflections      : 1
% 0.16/0.35  # Paramodulations                      : 270
% 0.16/0.35  # Factorizations                       : 0
% 0.16/0.35  # Equation resolutions                 : 3
% 0.16/0.35  # Propositional unsat checks           : 0
% 0.16/0.35  #    Propositional check models        : 0
% 0.16/0.35  #    Propositional check unsatisfiable : 0
% 0.16/0.35  #    Propositional clauses             : 0
% 0.16/0.35  #    Propositional clauses after purity: 0
% 0.16/0.35  #    Propositional unsat core size     : 0
% 0.16/0.35  #    Propositional preprocessing time  : 0.000
% 0.16/0.35  #    Propositional encoding time       : 0.000
% 0.16/0.35  #    Propositional solver time         : 0.000
% 0.16/0.35  #    Success case prop preproc time    : 0.000
% 0.16/0.35  #    Success case prop encoding time   : 0.000
% 0.16/0.35  #    Success case prop solver time     : 0.000
% 0.16/0.35  # Current number of processed clauses  : 39
% 0.16/0.35  #    Positive orientable unit clauses  : 18
% 0.16/0.35  #    Positive unorientable unit clauses: 3
% 0.16/0.35  #    Negative unit clauses             : 2
% 0.16/0.35  #    Non-unit-clauses                  : 16
% 0.16/0.35  # Current number of unprocessed clauses: 81
% 0.16/0.35  # ...number of literals in the above   : 92
% 0.16/0.35  # Current number of archived formulas  : 0
% 0.16/0.35  # Current number of archived clauses   : 16
% 0.16/0.35  # Clause-clause subsumption calls (NU) : 40
% 0.16/0.35  # Rec. Clause-clause subsumption calls : 35
% 0.16/0.35  # Non-unit clause-clause subsumptions  : 5
% 0.16/0.35  # Unit Clause-clause subsumption calls : 13
% 0.16/0.35  # Rewrite failures with RHS unbound    : 0
% 0.16/0.35  # BW rewrite match attempts            : 68
% 0.16/0.35  # BW rewrite match successes           : 56
% 0.16/0.35  # Condensation attempts                : 0
% 0.16/0.35  # Condensation successes               : 0
% 0.16/0.35  # Termbank termtop insertions          : 3415
% 0.16/0.35  
% 0.16/0.35  # -------------------------------------------------
% 0.16/0.35  # User time                : 0.031 s
% 0.16/0.35  # System time              : 0.004 s
% 0.16/0.35  # Total time               : 0.035 s
% 0.16/0.35  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
