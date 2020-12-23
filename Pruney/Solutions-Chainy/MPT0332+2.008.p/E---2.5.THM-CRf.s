%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:35 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 875 expanded)
%              Number of clauses        :   48 ( 358 expanded)
%              Number of leaves         :   18 ( 257 expanded)
%              Depth                    :   13
%              Number of atoms          :  110 ( 912 expanded)
%              Number of equality atoms :   74 ( 864 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t96_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t145_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_zfmisc_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t144_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_18,plain,(
    ! [X40,X41] : k3_tarski(k2_tarski(X40,X41)) = k2_xboole_0(X40,X41) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X22,X23] : k3_xboole_0(X22,X23) = k5_xboole_0(k5_xboole_0(X22,X23),k2_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_21,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X31,X32,X33,X34] : k3_enumset1(X31,X31,X32,X33,X34) = k2_enumset1(X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X15] : k3_xboole_0(X15,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X35,X36,X37,X38,X39] : k4_enumset1(X35,X35,X36,X37,X38,X39) = k3_enumset1(X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_31,plain,(
    ! [X14] : k2_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_32,plain,(
    ! [X16,X17] : k2_xboole_0(X16,k4_xboole_0(X17,X16)) = k2_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_33,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_36,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,plain,(
    ! [X18] : k5_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_39,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_40,plain,(
    ! [X24,X25] : r1_tarski(k4_xboole_0(X24,X25),k5_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t96_xboole_1])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_43,plain,(
    ! [X19,X20,X21] : k5_xboole_0(k5_xboole_0(X19,X20),X21) = k5_xboole_0(X19,k5_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k1_xboole_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_27]),c_0_28]),c_0_29]),c_0_36])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_48,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r2_hidden(X1,X3)
          & ~ r2_hidden(X2,X3)
          & X3 != k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t145_zfmisc_1])).

cnf(c_0_49,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)))))) = k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_27]),c_0_27]),c_0_42]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_35]),c_0_36]),c_0_36]),c_0_36])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_53,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_45,c_0_47])).

fof(c_0_54,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_55,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0)
    & ~ r2_hidden(esk2_0,esk3_0)
    & esk3_0 != k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_48])])])])).

cnf(c_0_56,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_42]),c_0_35]),c_0_36])).

cnf(c_0_57,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))))))) = k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_60,plain,(
    ! [X42,X43,X44] :
      ( r2_hidden(X42,X44)
      | r2_hidden(X43,X44)
      | X44 = k4_xboole_0(X44,k2_tarski(X42,X43)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).

cnf(c_0_61,negated_conjecture,
    ( esk3_0 != k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_62,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k2_xboole_0(X12,X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_63,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))))),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_51])).

cnf(c_0_64,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))))) = k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)) = k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_36]),c_0_36])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | X2 = k4_xboole_0(X2,k2_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( esk3_0 != k5_xboole_0(k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k5_xboole_0(k5_xboole_0(k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),k3_tarski(k4_enumset1(k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_22]),c_0_22]),c_0_27]),c_0_42]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))),k5_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_58])).

cnf(c_0_70,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(X1,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))))) = k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,plain,
    ( X2 = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k4_enumset1(X1,X1,X1,X1,X1,X3)),k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k4_enumset1(X1,X1,X1,X1,X1,X3)))))
    | r2_hidden(X3,X2)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_22]),c_0_42]),c_0_28]),c_0_29]),c_0_35]),c_0_36]),c_0_36]),c_0_36])).

cnf(c_0_72,negated_conjecture,
    ( k5_xboole_0(k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k3_tarski(k4_enumset1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))))))) != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_47]),c_0_65]),c_0_51])).

cnf(c_0_73,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_27]),c_0_28]),c_0_29]),c_0_36])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_51]),c_0_52]),c_0_45]),c_0_58])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X3),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k4_enumset1(X2,X2,X2,X2,X2,X3)))))) = X1
    | r2_hidden(X2,X1)
    | r2_hidden(X3,X1) ),
    inference(rw,[status(thm)],[c_0_71,c_0_51])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))) != esk3_0
    | ~ r1_tarski(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_52]),c_0_45]),c_0_47])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_65])).

cnf(c_0_78,plain,
    ( k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k3_tarski(k4_enumset1(X3,X3,X3,X3,X3,k4_enumset1(X1,X1,X1,X1,X1,X2)))) = X3
    | r2_hidden(X2,X3)
    | r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_75,c_0_58])).

cnf(c_0_79,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_80,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k4_enumset1(X2,X2,X2,X2,X2,X3))) = k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X3),X1)
    | r2_hidden(X2,X1)
    | r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_78])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_58,c_0_47])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_83,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_47]),c_0_81])]),c_0_82]),c_0_83]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:46:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.027 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.39  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.19/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.39  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.19/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.39  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.39  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.19/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.39  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.39  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.39  fof(t96_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_xboole_1)).
% 0.19/0.39  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.39  fof(t145_zfmisc_1, conjecture, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_zfmisc_1)).
% 0.19/0.39  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.39  fof(t144_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 0.19/0.39  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.39  fof(c_0_18, plain, ![X40, X41]:k3_tarski(k2_tarski(X40,X41))=k2_xboole_0(X40,X41), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.39  fof(c_0_19, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.39  fof(c_0_20, plain, ![X22, X23]:k3_xboole_0(X22,X23)=k5_xboole_0(k5_xboole_0(X22,X23),k2_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.19/0.39  cnf(c_0_21, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  fof(c_0_23, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.39  fof(c_0_24, plain, ![X31, X32, X33, X34]:k3_enumset1(X31,X31,X32,X33,X34)=k2_enumset1(X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.39  fof(c_0_25, plain, ![X15]:k3_xboole_0(X15,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.19/0.39  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  cnf(c_0_27, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.39  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_29, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.39  fof(c_0_30, plain, ![X35, X36, X37, X38, X39]:k4_enumset1(X35,X35,X36,X37,X38,X39)=k3_enumset1(X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.39  fof(c_0_31, plain, ![X14]:k2_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.39  fof(c_0_32, plain, ![X16, X17]:k2_xboole_0(X16,k4_xboole_0(X17,X16))=k2_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.19/0.39  fof(c_0_33, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.39  cnf(c_0_34, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 0.19/0.39  cnf(c_0_36, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.39  fof(c_0_37, plain, ![X18]:k5_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.39  cnf(c_0_38, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.39  fof(c_0_39, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k5_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.39  fof(c_0_40, plain, ![X24, X25]:r1_tarski(k4_xboole_0(X24,X25),k5_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t96_xboole_1])).
% 0.19/0.39  cnf(c_0_41, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.39  cnf(c_0_42, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.39  fof(c_0_43, plain, ![X19, X20, X21]:k5_xboole_0(k5_xboole_0(X19,X20),X21)=k5_xboole_0(X19,k5_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.39  cnf(c_0_44, plain, (k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k1_xboole_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.19/0.39  cnf(c_0_45, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.39  cnf(c_0_46, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_27]), c_0_28]), c_0_29]), c_0_36])).
% 0.19/0.39  cnf(c_0_47, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.39  fof(c_0_48, negated_conjecture, ~(![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2))))), inference(assume_negation,[status(cth)],[t145_zfmisc_1])).
% 0.19/0.39  cnf(c_0_49, plain, (r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.39  cnf(c_0_50, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))))))=k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_27]), c_0_27]), c_0_42]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_35]), c_0_36]), c_0_36]), c_0_36])).
% 0.19/0.39  cnf(c_0_51, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.39  cnf(c_0_52, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.19/0.39  cnf(c_0_53, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_45, c_0_47])).
% 0.19/0.39  fof(c_0_54, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k2_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.39  fof(c_0_55, negated_conjecture, ((~r2_hidden(esk1_0,esk3_0)&~r2_hidden(esk2_0,esk3_0))&esk3_0!=k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_48])])])])).
% 0.19/0.39  cnf(c_0_56, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_42]), c_0_35]), c_0_36])).
% 0.19/0.39  cnf(c_0_57, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)))))))=k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.39  cnf(c_0_58, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.19/0.39  cnf(c_0_59, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.39  fof(c_0_60, plain, ![X42, X43, X44]:(r2_hidden(X42,X44)|r2_hidden(X43,X44)|X44=k4_xboole_0(X44,k2_tarski(X42,X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).
% 0.19/0.39  cnf(c_0_61, negated_conjecture, (esk3_0!=k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.39  fof(c_0_62, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k2_xboole_0(X12,X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.39  cnf(c_0_63, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))))),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_56, c_0_51])).
% 0.19/0.39  cnf(c_0_64, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)))))=k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.39  cnf(c_0_65, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))=k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_36]), c_0_36])).
% 0.19/0.39  cnf(c_0_66, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|X2=k4_xboole_0(X2,k2_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.39  cnf(c_0_67, negated_conjecture, (esk3_0!=k5_xboole_0(k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k5_xboole_0(k5_xboole_0(k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),k3_tarski(k4_enumset1(k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_22]), c_0_22]), c_0_27]), c_0_42]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36])).
% 0.19/0.39  cnf(c_0_68, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.39  cnf(c_0_69, plain, (r1_tarski(k5_xboole_0(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))),k5_xboole_0(X2,X1))), inference(rw,[status(thm)],[c_0_63, c_0_58])).
% 0.19/0.39  cnf(c_0_70, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k5_xboole_0(X1,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))))=k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.39  cnf(c_0_71, plain, (X2=k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k4_enumset1(X1,X1,X1,X1,X1,X3)),k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k4_enumset1(X1,X1,X1,X1,X1,X3)))))|r2_hidden(X3,X2)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_22]), c_0_42]), c_0_28]), c_0_29]), c_0_35]), c_0_36]), c_0_36]), c_0_36])).
% 0.19/0.39  cnf(c_0_72, negated_conjecture, (k5_xboole_0(k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_xboole_0(k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))),k3_tarski(k4_enumset1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))))))))!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_47]), c_0_65]), c_0_51])).
% 0.19/0.39  cnf(c_0_73, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_27]), c_0_28]), c_0_29]), c_0_36])).
% 0.19/0.39  cnf(c_0_74, plain, (r1_tarski(X1,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_51]), c_0_52]), c_0_45]), c_0_58])).
% 0.19/0.39  cnf(c_0_75, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X3),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k4_enumset1(X2,X2,X2,X2,X2,X3))))))=X1|r2_hidden(X2,X1)|r2_hidden(X3,X1)), inference(rw,[status(thm)],[c_0_71, c_0_51])).
% 0.19/0.39  cnf(c_0_76, negated_conjecture, (k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))))!=esk3_0|~r1_tarski(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_52]), c_0_45]), c_0_47])).
% 0.19/0.39  cnf(c_0_77, plain, (r1_tarski(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_74, c_0_65])).
% 0.19/0.39  cnf(c_0_78, plain, (k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k3_tarski(k4_enumset1(X3,X3,X3,X3,X3,k4_enumset1(X1,X1,X1,X1,X1,X2))))=X3|r2_hidden(X2,X3)|r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_75, c_0_58])).
% 0.19/0.39  cnf(c_0_79, negated_conjecture, (k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))))!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77])])).
% 0.19/0.39  cnf(c_0_80, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k4_enumset1(X2,X2,X2,X2,X2,X3)))=k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X3),X1)|r2_hidden(X2,X1)|r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_58, c_0_78])).
% 0.19/0.39  cnf(c_0_81, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(spm,[status(thm)],[c_0_58, c_0_47])).
% 0.19/0.39  cnf(c_0_82, negated_conjecture, (~r2_hidden(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.39  cnf(c_0_83, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.39  cnf(c_0_84, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_47]), c_0_81])]), c_0_82]), c_0_83]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 85
% 0.19/0.39  # Proof object clause steps            : 48
% 0.19/0.39  # Proof object formula steps           : 37
% 0.19/0.39  # Proof object conjectures             : 11
% 0.19/0.39  # Proof object clause conjectures      : 8
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 20
% 0.19/0.39  # Proof object initial formulas used   : 18
% 0.19/0.39  # Proof object generating inferences   : 9
% 0.19/0.39  # Proof object simplifying inferences  : 100
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 18
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 20
% 0.19/0.39  # Removed in clause preprocessing      : 7
% 0.19/0.39  # Initial clauses in saturation        : 13
% 0.19/0.39  # Processed clauses                    : 371
% 0.19/0.39  # ...of these trivial                  : 27
% 0.19/0.39  # ...subsumed                          : 245
% 0.19/0.39  # ...remaining for further processing  : 99
% 0.19/0.39  # Other redundant clauses eliminated   : 0
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 15
% 0.19/0.39  # Generated clauses                    : 1593
% 0.19/0.39  # ...of the previous two non-trivial   : 1204
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 1593
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 0
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 71
% 0.19/0.39  #    Positive orientable unit clauses  : 21
% 0.19/0.39  #    Positive unorientable unit clauses: 5
% 0.19/0.39  #    Negative unit clauses             : 7
% 0.19/0.39  #    Non-unit-clauses                  : 38
% 0.19/0.39  # Current number of unprocessed clauses: 755
% 0.19/0.39  # ...number of literals in the above   : 1838
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 35
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 404
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 354
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 84
% 0.19/0.39  # Unit Clause-clause subsumption calls : 31
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 151
% 0.19/0.39  # BW rewrite match successes           : 83
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 23847
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.053 s
% 0.19/0.39  # System time              : 0.004 s
% 0.19/0.39  # Total time               : 0.057 s
% 0.19/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
