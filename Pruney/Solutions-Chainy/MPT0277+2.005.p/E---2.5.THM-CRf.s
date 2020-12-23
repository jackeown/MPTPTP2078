%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:05 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  132 (88118 expanded)
%              Number of clauses        :   99 (38828 expanded)
%              Number of leaves         :   16 (24364 expanded)
%              Depth                    :   29
%              Number of atoms          :  366 (134857 expanded)
%              Number of equality atoms :  288 (121838 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t75_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(X1,k2_tarski(X2,X3)) = k1_xboole_0
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t22_zfmisc_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(t69_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
      | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(c_0_16,plain,(
    ! [X15] : k4_xboole_0(k1_xboole_0,X15) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_17,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k4_xboole_0(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_19,plain,(
    ! [X16,X17] : k2_xboole_0(X16,X17) = k5_xboole_0(X16,k4_xboole_0(X17,X16)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_20,plain,(
    ! [X11,X12] : r1_tarski(k4_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(X1,k2_tarski(X2,X3)) = k1_xboole_0
      <=> ~ ( X1 != k1_xboole_0
            & X1 != k1_tarski(X2)
            & X1 != k1_tarski(X3)
            & X1 != k2_tarski(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t75_zfmisc_1])).

cnf(c_0_22,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X10] : k2_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,negated_conjecture,
    ( ( esk2_0 != k1_xboole_0
      | k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0)) != k1_xboole_0 )
    & ( esk2_0 != k1_tarski(esk3_0)
      | k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0)) != k1_xboole_0 )
    & ( esk2_0 != k1_tarski(esk4_0)
      | k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0)) != k1_xboole_0 )
    & ( esk2_0 != k2_tarski(esk3_0,esk4_0)
      | k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0)) != k1_xboole_0 )
    & ( k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0)) = k1_xboole_0
      | esk2_0 = k1_xboole_0
      | esk2_0 = k1_tarski(esk3_0)
      | esk2_0 = k1_tarski(esk4_0)
      | esk2_0 = k2_tarski(esk3_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])])).

fof(c_0_29,plain,(
    ! [X29] : k2_tarski(X29,X29) = k1_tarski(X29) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_30,plain,(
    ! [X30,X31] : k1_enumset1(X30,X30,X31) = k2_tarski(X30,X31) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_31,plain,(
    ! [X32,X33,X34] : k2_enumset1(X32,X32,X33,X34) = k1_enumset1(X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_32,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_33,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_23]),c_0_23])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_23])).

fof(c_0_37,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X18
        | X22 = X19
        | X22 = X20
        | X21 != k1_enumset1(X18,X19,X20) )
      & ( X23 != X18
        | r2_hidden(X23,X21)
        | X21 != k1_enumset1(X18,X19,X20) )
      & ( X23 != X19
        | r2_hidden(X23,X21)
        | X21 != k1_enumset1(X18,X19,X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k1_enumset1(X18,X19,X20) )
      & ( esk1_4(X24,X25,X26,X27) != X24
        | ~ r2_hidden(esk1_4(X24,X25,X26,X27),X27)
        | X27 = k1_enumset1(X24,X25,X26) )
      & ( esk1_4(X24,X25,X26,X27) != X25
        | ~ r2_hidden(esk1_4(X24,X25,X26,X27),X27)
        | X27 = k1_enumset1(X24,X25,X26) )
      & ( esk1_4(X24,X25,X26,X27) != X26
        | ~ r2_hidden(esk1_4(X24,X25,X26,X27),X27)
        | X27 = k1_enumset1(X24,X25,X26) )
      & ( r2_hidden(esk1_4(X24,X25,X26,X27),X27)
        | esk1_4(X24,X25,X26,X27) = X24
        | esk1_4(X24,X25,X26,X27) = X25
        | esk1_4(X24,X25,X26,X27) = X26
        | X27 = k1_enumset1(X24,X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_38,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_27,c_0_23])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0)) = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk2_0 = k1_tarski(esk3_0)
    | esk2_0 = k1_tarski(esk4_0)
    | esk2_0 = k2_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk2_0 = k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)
    | esk2_0 = k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)
    | esk2_0 = k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)
    | k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_23]),c_0_42]),c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_45,c_0_33])).

fof(c_0_51,plain,(
    ! [X38,X39] : k4_xboole_0(k1_tarski(X38),k2_tarski(X38,X39)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t22_zfmisc_1])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[c_0_46,c_0_42])).

cnf(c_0_54,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = esk2_0
    | k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = esk2_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) = esk2_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = esk2_0
    | esk2_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_42])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).

cnf(c_0_59,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = esk2_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) = esk2_0
    | k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = esk2_0
    | esk2_0 = k1_xboole_0
    | r1_tarski(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_40]),c_0_41]),c_0_41]),c_0_23]),c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_57])])).

cnf(c_0_62,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) = esk2_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = esk2_0
    | esk2_0 = k1_xboole_0
    | r2_hidden(esk4_0,esk2_0)
    | r1_tarski(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_49]),c_0_50])).

cnf(c_0_64,negated_conjecture,
    ( esk2_0 != k1_tarski(esk3_0)
    | k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_65,plain,
    ( k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_60]),c_0_49]),c_0_50])).

cnf(c_0_66,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = esk2_0
    | esk2_0 = k1_xboole_0
    | r2_hidden(esk4_0,esk2_0)
    | r1_tarski(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_63]),c_0_49]),c_0_50])).

fof(c_0_68,plain,(
    ! [X35,X36,X37] :
      ( ( ~ r1_tarski(X35,k2_tarski(X36,X37))
        | X35 = k1_xboole_0
        | X35 = k1_tarski(X36)
        | X35 = k1_tarski(X37)
        | X35 = k2_tarski(X36,X37) )
      & ( X35 != k1_xboole_0
        | r1_tarski(X35,k2_tarski(X36,X37)) )
      & ( X35 != k1_tarski(X36)
        | r1_tarski(X35,k2_tarski(X36,X37)) )
      & ( X35 != k1_tarski(X37)
        | r1_tarski(X35,k2_tarski(X36,X37)) )
      & ( X35 != k2_tarski(X36,X37)
        | r1_tarski(X35,k2_tarski(X36,X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

cnf(c_0_69,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_70,negated_conjecture,
    ( esk2_0 != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)
    | k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_40]),c_0_41]),c_0_41]),c_0_23]),c_0_42]),c_0_42])).

cnf(c_0_71,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,X1)) = esk2_0
    | esk2_0 = k1_xboole_0
    | r2_hidden(esk4_0,esk2_0)
    | r1_tarski(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_63,c_0_67])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_41]),c_0_23]),c_0_42])).

cnf(c_0_75,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r2_hidden(esk4_0,esk2_0)
    | r1_tarski(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])]),c_0_66])).

fof(c_0_76,plain,(
    ! [X40,X41] :
      ( k4_xboole_0(k1_tarski(X40),X41) = k1_xboole_0
      | k4_xboole_0(k1_tarski(X40),X41) = k1_tarski(X40) ) ),
    inference(variable_rename,[status(thm)],[t69_zfmisc_1])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X3,X3,X3,X3)
    | X1 = k2_enumset1(X2,X2,X2,X3)
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0)
    | r1_tarski(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_44]),c_0_50])])).

cnf(c_0_79,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = esk2_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) = esk2_0
    | k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = esk2_0
    | esk2_0 = k1_xboole_0
    | r2_hidden(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

fof(c_0_81,plain,(
    ! [X42,X43,X44] :
      ( ( ~ r2_hidden(X42,X44)
        | k4_xboole_0(k2_tarski(X42,X43),X44) != k2_tarski(X42,X43) )
      & ( ~ r2_hidden(X43,X44)
        | k4_xboole_0(k2_tarski(X42,X43),X44) != k2_tarski(X42,X43) )
      & ( r2_hidden(X42,X44)
        | r2_hidden(X43,X44)
        | k4_xboole_0(k2_tarski(X42,X43),X44) = k2_tarski(X42,X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

cnf(c_0_82,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)) = k1_xboole_0
    | k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_23]),c_0_23]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_83,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) = esk2_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = esk2_0
    | esk2_0 = k1_xboole_0
    | r2_hidden(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_80])).

cnf(c_0_84,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k2_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_85,plain,
    ( k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) = k2_enumset1(X1,X1,X1,X1)
    | k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_82]),c_0_34])).

cnf(c_0_86,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = esk2_0
    | esk2_0 = k1_xboole_0
    | r2_hidden(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_83])).

cnf(c_0_87,plain,
    ( k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X3)) = k2_enumset1(X2,X2,X2,X2)
    | k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X3)) = k2_enumset1(X2,X2,X2,X3)
    | k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X3)) = k2_enumset1(X3,X3,X3,X3)
    | k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X3)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_54])).

cnf(c_0_88,plain,
    ( k5_xboole_0(k2_enumset1(X3,X3,X3,X1),k3_xboole_0(k2_enumset1(X3,X3,X3,X1),X2)) != k2_enumset1(X3,X3,X3,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_41]),c_0_41]),c_0_23]),c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_89,negated_conjecture,
    ( k3_xboole_0(esk2_0,X1) = k1_xboole_0
    | k3_xboole_0(esk2_0,X1) = esk2_0
    | esk2_0 = k1_xboole_0
    | r2_hidden(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)
    | k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)
    | k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = k1_xboole_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = esk2_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) = esk2_0
    | k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = esk2_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r2_hidden(esk4_0,esk2_0)
    | k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)) != esk2_0
    | ~ r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | r2_hidden(esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_89]),c_0_72])]),c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( esk2_0 != k1_tarski(esk4_0)
    | k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_94,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)
    | k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = k1_xboole_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = esk2_0
    | k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = esk2_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) = esk2_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r2_hidden(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_50]),c_0_58])])).

cnf(c_0_96,negated_conjecture,
    ( esk2_0 != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)
    | k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_40]),c_0_41]),c_0_41]),c_0_23]),c_0_42]),c_0_42])).

cnf(c_0_97,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k3_xboole_0(X3,k2_enumset1(X1,X1,X1,X2))) != k2_enumset1(X1,X1,X1,X2)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_88,c_0_43])).

cnf(c_0_98,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = k1_xboole_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) = esk2_0
    | k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = esk2_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = esk2_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_95]),c_0_44]),c_0_50])])).

cnf(c_0_100,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)
    | k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)
    | k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = k1_xboole_0
    | k5_xboole_0(esk2_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) != k1_xboole_0
    | k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) != esk2_0 ),
    inference(spm,[status(thm)],[c_0_96,c_0_87])).

cnf(c_0_101,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = esk2_0
    | k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = esk2_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) = esk2_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_50]),c_0_99])])).

cnf(c_0_102,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)
    | k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)
    | k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = k1_xboole_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) = esk2_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = esk2_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_72])])).

cnf(c_0_103,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) = esk2_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = esk2_0
    | k3_xboole_0(esk2_0,X1) = k1_xboole_0
    | k3_xboole_0(esk2_0,X1) = esk2_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_85,c_0_101])).

cnf(c_0_104,negated_conjecture,
    ( esk2_0 != k2_tarski(esk3_0,esk4_0)
    | k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_105,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X4)
    | esk1_4(X1,X2,X3,X4) = X1
    | esk1_4(X1,X2,X3,X4) = X2
    | esk1_4(X1,X2,X3,X4) = X3
    | X4 = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_106,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_107,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = k1_xboole_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) = esk2_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = esk2_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_108,plain,
    ( X4 = k1_enumset1(X1,X2,X3)
    | esk1_4(X1,X2,X3,X4) != X3
    | ~ r2_hidden(esk1_4(X1,X2,X3,X4),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_109,negated_conjecture,
    ( esk2_0 != k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)
    | k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_41]),c_0_41]),c_0_23]),c_0_42]),c_0_42])).

cnf(c_0_110,plain,
    ( X4 = k2_enumset1(X1,X1,X2,X3)
    | esk1_4(X1,X2,X3,X4) = X3
    | esk1_4(X1,X2,X3,X4) = X2
    | esk1_4(X1,X2,X3,X4) = X1
    | r2_hidden(esk1_4(X1,X2,X3,X4),X4) ),
    inference(rw,[status(thm)],[c_0_105,c_0_42])).

cnf(c_0_111,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_106,c_0_42])).

cnf(c_0_112,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = esk2_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) = esk2_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_107]),c_0_50]),c_0_99])])).

cnf(c_0_113,plain,
    ( X4 = k2_enumset1(X1,X1,X2,X3)
    | esk1_4(X1,X2,X3,X4) != X3
    | ~ r2_hidden(esk1_4(X1,X2,X3,X4),X4) ),
    inference(rw,[status(thm)],[c_0_108,c_0_42])).

cnf(c_0_114,negated_conjecture,
    ( esk1_4(esk3_0,esk3_0,esk4_0,esk2_0) = esk3_0
    | esk1_4(esk3_0,esk3_0,esk4_0,esk2_0) = esk4_0
    | r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110])]),c_0_63])])).

cnf(c_0_115,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k2_enumset1(X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_111])).

cnf(c_0_116,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = esk2_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_112]),c_0_63])])).

cnf(c_0_117,plain,
    ( X4 = k1_enumset1(X1,X2,X3)
    | esk1_4(X1,X2,X3,X4) != X2
    | ~ r2_hidden(esk1_4(X1,X2,X3,X4),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_118,negated_conjecture,
    ( esk1_4(esk3_0,esk3_0,esk4_0,esk2_0) = esk3_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) = esk2_0
    | r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_99])])).

cnf(c_0_119,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | X1 = esk3_0
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_120,plain,
    ( X4 = k2_enumset1(X1,X1,X2,X3)
    | esk1_4(X1,X2,X3,X4) != X2
    | ~ r2_hidden(esk1_4(X1,X2,X3,X4),X4) ),
    inference(rw,[status(thm)],[c_0_117,c_0_42])).

cnf(c_0_121,negated_conjecture,
    ( esk1_4(esk3_0,esk3_0,esk4_0,esk2_0) = esk3_0
    | r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_118]),c_0_63])])).

cnf(c_0_122,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r2_hidden(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_116])).

cnf(c_0_123,negated_conjecture,
    ( esk4_0 = esk3_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_119,c_0_99])).

cnf(c_0_124,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) = esk2_0
    | r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk2_0),esk2_0)
    | ~ r2_hidden(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_122]),c_0_44]),c_0_50])])).

cnf(c_0_126,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_123]),c_0_116])).

cnf(c_0_127,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) = esk2_0
    | r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_125])])).

cnf(c_0_128,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_116]),c_0_63])])).

cnf(c_0_129,plain,
    ( k2_enumset1(X1,X1,X1,X2) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_63]),c_0_61])])).

cnf(c_0_130,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_44]),c_0_50])])).

cnf(c_0_131,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_128]),c_0_128]),c_0_128]),c_0_129]),c_0_130]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.42/0.60  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.42/0.60  # and selection function SelectNegativeLiterals.
% 0.42/0.60  #
% 0.42/0.60  # Preprocessing time       : 0.028 s
% 0.42/0.60  # Presaturation interreduction done
% 0.42/0.60  
% 0.42/0.60  # Proof found!
% 0.42/0.60  # SZS status Theorem
% 0.42/0.60  # SZS output start CNFRefutation
% 0.42/0.60  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.42/0.60  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.42/0.60  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.42/0.60  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.42/0.60  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.42/0.60  fof(t75_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(X1,k2_tarski(X2,X3))=k1_xboole_0<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 0.42/0.60  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.42/0.60  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.42/0.60  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.42/0.60  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.42/0.60  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.42/0.60  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.42/0.60  fof(t22_zfmisc_1, axiom, ![X1, X2]:k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 0.42/0.60  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 0.42/0.60  fof(t69_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 0.42/0.60  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 0.42/0.60  fof(c_0_16, plain, ![X15]:k4_xboole_0(k1_xboole_0,X15)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.42/0.60  fof(c_0_17, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.42/0.60  fof(c_0_18, plain, ![X13, X14]:k4_xboole_0(X13,k4_xboole_0(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.42/0.60  fof(c_0_19, plain, ![X16, X17]:k2_xboole_0(X16,X17)=k5_xboole_0(X16,k4_xboole_0(X17,X16)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.42/0.60  fof(c_0_20, plain, ![X11, X12]:r1_tarski(k4_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.42/0.60  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(X1,k2_tarski(X2,X3))=k1_xboole_0<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3))))), inference(assume_negation,[status(cth)],[t75_zfmisc_1])).
% 0.42/0.60  cnf(c_0_22, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.42/0.60  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.42/0.60  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.42/0.60  fof(c_0_25, plain, ![X10]:k2_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.42/0.60  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.60  cnf(c_0_27, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.42/0.60  fof(c_0_28, negated_conjecture, (((((esk2_0!=k1_xboole_0|k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0))!=k1_xboole_0)&(esk2_0!=k1_tarski(esk3_0)|k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0))!=k1_xboole_0))&(esk2_0!=k1_tarski(esk4_0)|k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0))!=k1_xboole_0))&(esk2_0!=k2_tarski(esk3_0,esk4_0)|k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0))!=k1_xboole_0))&(k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0))=k1_xboole_0|(esk2_0=k1_xboole_0|esk2_0=k1_tarski(esk3_0)|esk2_0=k1_tarski(esk4_0)|esk2_0=k2_tarski(esk3_0,esk4_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])])).
% 0.42/0.60  fof(c_0_29, plain, ![X29]:k2_tarski(X29,X29)=k1_tarski(X29), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.42/0.60  fof(c_0_30, plain, ![X30, X31]:k1_enumset1(X30,X30,X31)=k2_tarski(X30,X31), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.42/0.60  fof(c_0_31, plain, ![X32, X33, X34]:k2_enumset1(X32,X32,X33,X34)=k1_enumset1(X32,X33,X34), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.42/0.60  fof(c_0_32, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.42/0.60  cnf(c_0_33, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.42/0.60  cnf(c_0_34, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_23]), c_0_23])).
% 0.42/0.60  cnf(c_0_35, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.42/0.60  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_26, c_0_23])).
% 0.42/0.60  fof(c_0_37, plain, ![X18, X19, X20, X21, X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X22,X21)|(X22=X18|X22=X19|X22=X20)|X21!=k1_enumset1(X18,X19,X20))&(((X23!=X18|r2_hidden(X23,X21)|X21!=k1_enumset1(X18,X19,X20))&(X23!=X19|r2_hidden(X23,X21)|X21!=k1_enumset1(X18,X19,X20)))&(X23!=X20|r2_hidden(X23,X21)|X21!=k1_enumset1(X18,X19,X20))))&((((esk1_4(X24,X25,X26,X27)!=X24|~r2_hidden(esk1_4(X24,X25,X26,X27),X27)|X27=k1_enumset1(X24,X25,X26))&(esk1_4(X24,X25,X26,X27)!=X25|~r2_hidden(esk1_4(X24,X25,X26,X27),X27)|X27=k1_enumset1(X24,X25,X26)))&(esk1_4(X24,X25,X26,X27)!=X26|~r2_hidden(esk1_4(X24,X25,X26,X27),X27)|X27=k1_enumset1(X24,X25,X26)))&(r2_hidden(esk1_4(X24,X25,X26,X27),X27)|(esk1_4(X24,X25,X26,X27)=X24|esk1_4(X24,X25,X26,X27)=X25|esk1_4(X24,X25,X26,X27)=X26)|X27=k1_enumset1(X24,X25,X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.42/0.60  cnf(c_0_38, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_27, c_0_23])).
% 0.42/0.60  cnf(c_0_39, negated_conjecture, (k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0))=k1_xboole_0|esk2_0=k1_xboole_0|esk2_0=k1_tarski(esk3_0)|esk2_0=k1_tarski(esk4_0)|esk2_0=k2_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.42/0.60  cnf(c_0_40, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.42/0.60  cnf(c_0_41, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.42/0.60  cnf(c_0_42, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.42/0.60  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.42/0.60  cnf(c_0_44, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.42/0.60  cnf(c_0_45, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.42/0.60  cnf(c_0_46, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.42/0.60  cnf(c_0_47, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_38, c_0_34])).
% 0.42/0.60  cnf(c_0_48, negated_conjecture, (esk2_0=k1_xboole_0|esk2_0=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)|esk2_0=k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)|esk2_0=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)|k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_23]), c_0_42]), c_0_42]), c_0_42]), c_0_42])).
% 0.42/0.60  cnf(c_0_49, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.42/0.60  cnf(c_0_50, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_45, c_0_33])).
% 0.42/0.60  fof(c_0_51, plain, ![X38, X39]:k4_xboole_0(k1_tarski(X38),k2_tarski(X38,X39))=k1_xboole_0, inference(variable_rename,[status(thm)],[t22_zfmisc_1])).
% 0.42/0.60  cnf(c_0_52, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.42/0.60  cnf(c_0_53, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X4,X5)), inference(rw,[status(thm)],[c_0_46, c_0_42])).
% 0.42/0.60  cnf(c_0_54, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_47, c_0_43])).
% 0.42/0.60  cnf(c_0_55, negated_conjecture, (k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=esk2_0|k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=esk2_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)=esk2_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=esk2_0|esk2_0=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_48]), c_0_49]), c_0_50])).
% 0.42/0.60  cnf(c_0_56, plain, (k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.42/0.60  cnf(c_0_57, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X5,X2)), inference(rw,[status(thm)],[c_0_52, c_0_42])).
% 0.42/0.60  cnf(c_0_58, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).
% 0.42/0.60  cnf(c_0_59, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=esk2_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)=esk2_0|k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=esk2_0|esk2_0=k1_xboole_0|r1_tarski(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.42/0.60  cnf(c_0_60, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_40]), c_0_41]), c_0_41]), c_0_23]), c_0_42]), c_0_42]), c_0_42])).
% 0.42/0.60  cnf(c_0_61, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_57])])).
% 0.42/0.60  cnf(c_0_62, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)=esk2_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=esk2_0|esk2_0=k1_xboole_0|r2_hidden(esk4_0,esk2_0)|r1_tarski(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.42/0.60  cnf(c_0_63, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_49]), c_0_50])).
% 0.42/0.60  cnf(c_0_64, negated_conjecture, (esk2_0!=k1_tarski(esk3_0)|k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.42/0.60  cnf(c_0_65, plain, (k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_60]), c_0_49]), c_0_50])).
% 0.42/0.60  cnf(c_0_66, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=esk2_0|esk2_0=k1_xboole_0|r2_hidden(esk4_0,esk2_0)|r1_tarski(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.42/0.60  cnf(c_0_67, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_63]), c_0_49]), c_0_50])).
% 0.42/0.60  fof(c_0_68, plain, ![X35, X36, X37]:((~r1_tarski(X35,k2_tarski(X36,X37))|(X35=k1_xboole_0|X35=k1_tarski(X36)|X35=k1_tarski(X37)|X35=k2_tarski(X36,X37)))&((((X35!=k1_xboole_0|r1_tarski(X35,k2_tarski(X36,X37)))&(X35!=k1_tarski(X36)|r1_tarski(X35,k2_tarski(X36,X37))))&(X35!=k1_tarski(X37)|r1_tarski(X35,k2_tarski(X36,X37))))&(X35!=k2_tarski(X36,X37)|r1_tarski(X35,k2_tarski(X36,X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 0.42/0.60  cnf(c_0_69, negated_conjecture, (esk2_0!=k1_xboole_0|k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.42/0.60  cnf(c_0_70, negated_conjecture, (esk2_0!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)|k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_40]), c_0_41]), c_0_41]), c_0_23]), c_0_42]), c_0_42])).
% 0.42/0.60  cnf(c_0_71, negated_conjecture, (k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,X1))=esk2_0|esk2_0=k1_xboole_0|r2_hidden(esk4_0,esk2_0)|r1_tarski(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.42/0.60  cnf(c_0_72, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_63, c_0_67])).
% 0.42/0.60  cnf(c_0_73, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k2_tarski(X2,X3)|~r1_tarski(X1,k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.42/0.60  cnf(c_0_74, negated_conjecture, (esk2_0!=k1_xboole_0|k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_41]), c_0_23]), c_0_42])).
% 0.42/0.60  cnf(c_0_75, negated_conjecture, (esk2_0=k1_xboole_0|r2_hidden(esk4_0,esk2_0)|r1_tarski(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])]), c_0_66])).
% 0.42/0.60  fof(c_0_76, plain, ![X40, X41]:(k4_xboole_0(k1_tarski(X40),X41)=k1_xboole_0|k4_xboole_0(k1_tarski(X40),X41)=k1_tarski(X40)), inference(variable_rename,[status(thm)],[t69_zfmisc_1])).
% 0.42/0.60  cnf(c_0_77, plain, (X1=k1_xboole_0|X1=k2_enumset1(X3,X3,X3,X3)|X1=k2_enumset1(X2,X2,X2,X3)|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42])).
% 0.42/0.60  cnf(c_0_78, negated_conjecture, (r2_hidden(esk4_0,esk2_0)|r1_tarski(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_44]), c_0_50])])).
% 0.42/0.60  cnf(c_0_79, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.42/0.60  cnf(c_0_80, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=esk2_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)=esk2_0|k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=esk2_0|esk2_0=k1_xboole_0|r2_hidden(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.42/0.60  fof(c_0_81, plain, ![X42, X43, X44]:(((~r2_hidden(X42,X44)|k4_xboole_0(k2_tarski(X42,X43),X44)!=k2_tarski(X42,X43))&(~r2_hidden(X43,X44)|k4_xboole_0(k2_tarski(X42,X43),X44)!=k2_tarski(X42,X43)))&(r2_hidden(X42,X44)|r2_hidden(X43,X44)|k4_xboole_0(k2_tarski(X42,X43),X44)=k2_tarski(X42,X43))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 0.42/0.60  cnf(c_0_82, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2))=k1_xboole_0|k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2))=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_23]), c_0_23]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42])).
% 0.42/0.60  cnf(c_0_83, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)=esk2_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=esk2_0|esk2_0=k1_xboole_0|r2_hidden(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_58, c_0_80])).
% 0.42/0.60  cnf(c_0_84, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)!=k2_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.42/0.60  cnf(c_0_85, plain, (k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)=k2_enumset1(X1,X1,X1,X1)|k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_82]), c_0_34])).
% 0.42/0.60  cnf(c_0_86, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=esk2_0|esk2_0=k1_xboole_0|r2_hidden(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_61, c_0_83])).
% 0.42/0.60  cnf(c_0_87, plain, (k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X3))=k2_enumset1(X2,X2,X2,X2)|k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X3))=k2_enumset1(X2,X2,X2,X3)|k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X3))=k2_enumset1(X3,X3,X3,X3)|k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X3))=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_54])).
% 0.42/0.60  cnf(c_0_88, plain, (k5_xboole_0(k2_enumset1(X3,X3,X3,X1),k3_xboole_0(k2_enumset1(X3,X3,X3,X1),X2))!=k2_enumset1(X3,X3,X3,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_41]), c_0_41]), c_0_23]), c_0_42]), c_0_42]), c_0_42])).
% 0.42/0.60  cnf(c_0_89, negated_conjecture, (k3_xboole_0(esk2_0,X1)=k1_xboole_0|k3_xboole_0(esk2_0,X1)=esk2_0|esk2_0=k1_xboole_0|r2_hidden(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.42/0.60  cnf(c_0_90, negated_conjecture, (k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)|k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)|k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=k1_xboole_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=esk2_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)=esk2_0|k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=esk2_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_87])).
% 0.42/0.60  cnf(c_0_91, negated_conjecture, (esk2_0=k1_xboole_0|r2_hidden(esk4_0,esk2_0)|k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))!=esk2_0|~r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_88, c_0_86])).
% 0.42/0.60  cnf(c_0_92, negated_conjecture, (k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=k1_xboole_0|esk2_0=k1_xboole_0|r2_hidden(esk4_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_89]), c_0_72])]), c_0_86])).
% 0.42/0.60  cnf(c_0_93, negated_conjecture, (esk2_0!=k1_tarski(esk4_0)|k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.42/0.60  cnf(c_0_94, negated_conjecture, (k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)|k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=k1_xboole_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=esk2_0|k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=esk2_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)=esk2_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_90])).
% 0.42/0.60  cnf(c_0_95, negated_conjecture, (esk2_0=k1_xboole_0|r2_hidden(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_50]), c_0_58])])).
% 0.42/0.60  cnf(c_0_96, negated_conjecture, (esk2_0!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)|k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_40]), c_0_41]), c_0_41]), c_0_23]), c_0_42]), c_0_42])).
% 0.42/0.60  cnf(c_0_97, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X2),k3_xboole_0(X3,k2_enumset1(X1,X1,X1,X2)))!=k2_enumset1(X1,X1,X1,X2)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_88, c_0_43])).
% 0.42/0.60  cnf(c_0_98, negated_conjecture, (k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=k1_xboole_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)=esk2_0|k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=esk2_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=esk2_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_94])).
% 0.42/0.60  cnf(c_0_99, negated_conjecture, (r2_hidden(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_95]), c_0_44]), c_0_50])])).
% 0.42/0.60  cnf(c_0_100, negated_conjecture, (k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)|k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)|k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=k1_xboole_0|k5_xboole_0(esk2_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))!=k1_xboole_0|k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)!=esk2_0), inference(spm,[status(thm)],[c_0_96, c_0_87])).
% 0.42/0.60  cnf(c_0_101, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=esk2_0|k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=esk2_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)=esk2_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_50]), c_0_99])])).
% 0.42/0.60  cnf(c_0_102, negated_conjecture, (k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)|k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)|k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=k1_xboole_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)=esk2_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=esk2_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_72])])).
% 0.42/0.60  cnf(c_0_103, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)=esk2_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=esk2_0|k3_xboole_0(esk2_0,X1)=k1_xboole_0|k3_xboole_0(esk2_0,X1)=esk2_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_85, c_0_101])).
% 0.42/0.60  cnf(c_0_104, negated_conjecture, (esk2_0!=k2_tarski(esk3_0,esk4_0)|k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk4_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.42/0.60  cnf(c_0_105, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X4)|esk1_4(X1,X2,X3,X4)=X1|esk1_4(X1,X2,X3,X4)=X2|esk1_4(X1,X2,X3,X4)=X3|X4=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.42/0.60  cnf(c_0_106, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.42/0.60  cnf(c_0_107, negated_conjecture, (k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=k1_xboole_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)=esk2_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=esk2_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.42/0.60  cnf(c_0_108, plain, (X4=k1_enumset1(X1,X2,X3)|esk1_4(X1,X2,X3,X4)!=X3|~r2_hidden(esk1_4(X1,X2,X3,X4),X4)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.42/0.60  cnf(c_0_109, negated_conjecture, (esk2_0!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)|k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_41]), c_0_41]), c_0_23]), c_0_42]), c_0_42])).
% 0.42/0.60  cnf(c_0_110, plain, (X4=k2_enumset1(X1,X1,X2,X3)|esk1_4(X1,X2,X3,X4)=X3|esk1_4(X1,X2,X3,X4)=X2|esk1_4(X1,X2,X3,X4)=X1|r2_hidden(esk1_4(X1,X2,X3,X4),X4)), inference(rw,[status(thm)],[c_0_105, c_0_42])).
% 0.42/0.60  cnf(c_0_111, plain, (X1=X5|X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_106, c_0_42])).
% 0.42/0.60  cnf(c_0_112, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=esk2_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)=esk2_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_107]), c_0_50]), c_0_99])])).
% 0.42/0.60  cnf(c_0_113, plain, (X4=k2_enumset1(X1,X1,X2,X3)|esk1_4(X1,X2,X3,X4)!=X3|~r2_hidden(esk1_4(X1,X2,X3,X4),X4)), inference(rw,[status(thm)],[c_0_108, c_0_42])).
% 0.42/0.60  cnf(c_0_114, negated_conjecture, (esk1_4(esk3_0,esk3_0,esk4_0,esk2_0)=esk3_0|esk1_4(esk3_0,esk3_0,esk4_0,esk2_0)=esk4_0|r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110])]), c_0_63])])).
% 0.42/0.60  cnf(c_0_115, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k2_enumset1(X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_111])).
% 0.42/0.60  cnf(c_0_116, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=esk2_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_112]), c_0_63])])).
% 0.42/0.60  cnf(c_0_117, plain, (X4=k1_enumset1(X1,X2,X3)|esk1_4(X1,X2,X3,X4)!=X2|~r2_hidden(esk1_4(X1,X2,X3,X4),X4)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.42/0.60  cnf(c_0_118, negated_conjecture, (esk1_4(esk3_0,esk3_0,esk4_0,esk2_0)=esk3_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)=esk2_0|r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_99])])).
% 0.42/0.60  cnf(c_0_119, negated_conjecture, (esk2_0=k1_xboole_0|X1=esk3_0|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 0.42/0.60  cnf(c_0_120, plain, (X4=k2_enumset1(X1,X1,X2,X3)|esk1_4(X1,X2,X3,X4)!=X2|~r2_hidden(esk1_4(X1,X2,X3,X4),X4)), inference(rw,[status(thm)],[c_0_117, c_0_42])).
% 0.42/0.60  cnf(c_0_121, negated_conjecture, (esk1_4(esk3_0,esk3_0,esk4_0,esk2_0)=esk3_0|r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_118]), c_0_63])])).
% 0.42/0.60  cnf(c_0_122, negated_conjecture, (esk2_0=k1_xboole_0|r2_hidden(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_58, c_0_116])).
% 0.42/0.60  cnf(c_0_123, negated_conjecture, (esk4_0=esk3_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_119, c_0_99])).
% 0.42/0.60  cnf(c_0_124, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)=esk2_0|r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk2_0),esk2_0)|~r2_hidden(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 0.42/0.60  cnf(c_0_125, negated_conjecture, (r2_hidden(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_122]), c_0_44]), c_0_50])])).
% 0.42/0.60  cnf(c_0_126, negated_conjecture, (esk2_0=k1_xboole_0|k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_123]), c_0_116])).
% 0.42/0.60  cnf(c_0_127, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)=esk2_0|r2_hidden(esk1_4(esk3_0,esk3_0,esk4_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_125])])).
% 0.42/0.60  cnf(c_0_128, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_116]), c_0_63])])).
% 0.42/0.60  cnf(c_0_129, plain, (k2_enumset1(X1,X1,X1,X2)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_63]), c_0_61])])).
% 0.42/0.60  cnf(c_0_130, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_44]), c_0_50])])).
% 0.42/0.60  cnf(c_0_131, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_128]), c_0_128]), c_0_128]), c_0_129]), c_0_130]), ['proof']).
% 0.42/0.60  # SZS output end CNFRefutation
% 0.42/0.60  # Proof object total steps             : 132
% 0.42/0.60  # Proof object clause steps            : 99
% 0.42/0.60  # Proof object formula steps           : 33
% 0.42/0.60  # Proof object conjectures             : 50
% 0.42/0.60  # Proof object clause conjectures      : 47
% 0.42/0.60  # Proof object formula conjectures     : 3
% 0.42/0.60  # Proof object initial clauses used    : 25
% 0.42/0.60  # Proof object initial formulas used   : 16
% 0.42/0.60  # Proof object generating inferences   : 47
% 0.42/0.60  # Proof object simplifying inferences  : 143
% 0.42/0.60  # Training examples: 0 positive, 0 negative
% 0.42/0.60  # Parsed axioms                        : 16
% 0.42/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.42/0.60  # Initial clauses                      : 33
% 0.42/0.60  # Removed in clause preprocessing      : 5
% 0.42/0.60  # Initial clauses in saturation        : 28
% 0.42/0.60  # Processed clauses                    : 1411
% 0.42/0.60  # ...of these trivial                  : 56
% 0.42/0.60  # ...subsumed                          : 900
% 0.42/0.60  # ...remaining for further processing  : 455
% 0.42/0.60  # Other redundant clauses eliminated   : 510
% 0.42/0.60  # Clauses deleted for lack of memory   : 0
% 0.42/0.60  # Backward-subsumed                    : 151
% 0.42/0.60  # Backward-rewritten                   : 139
% 0.42/0.60  # Generated clauses                    : 15237
% 0.42/0.60  # ...of the previous two non-trivial   : 11934
% 0.42/0.60  # Contextual simplify-reflections      : 7
% 0.42/0.60  # Paramodulations                      : 14579
% 0.42/0.60  # Factorizations                       : 143
% 0.42/0.60  # Equation resolutions                 : 518
% 0.42/0.60  # Propositional unsat checks           : 0
% 0.42/0.60  #    Propositional check models        : 0
% 0.42/0.60  #    Propositional check unsatisfiable : 0
% 0.42/0.60  #    Propositional clauses             : 0
% 0.42/0.60  #    Propositional clauses after purity: 0
% 0.42/0.60  #    Propositional unsat core size     : 0
% 0.42/0.60  #    Propositional preprocessing time  : 0.000
% 0.42/0.60  #    Propositional encoding time       : 0.000
% 0.42/0.60  #    Propositional solver time         : 0.000
% 0.42/0.60  #    Success case prop preproc time    : 0.000
% 0.42/0.60  #    Success case prop encoding time   : 0.000
% 0.42/0.60  #    Success case prop solver time     : 0.000
% 0.42/0.60  # Current number of processed clauses  : 129
% 0.42/0.60  #    Positive orientable unit clauses  : 25
% 0.42/0.60  #    Positive unorientable unit clauses: 1
% 0.42/0.60  #    Negative unit clauses             : 6
% 0.42/0.60  #    Non-unit-clauses                  : 97
% 0.42/0.60  # Current number of unprocessed clauses: 9950
% 0.42/0.60  # ...number of literals in the above   : 67737
% 0.42/0.60  # Current number of archived formulas  : 0
% 0.42/0.60  # Current number of archived clauses   : 323
% 0.42/0.60  # Clause-clause subsumption calls (NU) : 8931
% 0.42/0.60  # Rec. Clause-clause subsumption calls : 5210
% 0.42/0.60  # Non-unit clause-clause subsumptions  : 713
% 0.42/0.60  # Unit Clause-clause subsumption calls : 378
% 0.42/0.60  # Rewrite failures with RHS unbound    : 0
% 0.42/0.60  # BW rewrite match attempts            : 93
% 0.42/0.60  # BW rewrite match successes           : 33
% 0.42/0.60  # Condensation attempts                : 0
% 0.42/0.60  # Condensation successes               : 0
% 0.42/0.60  # Termbank termtop insertions          : 367367
% 0.42/0.60  
% 0.42/0.60  # -------------------------------------------------
% 0.42/0.60  # User time                : 0.252 s
% 0.42/0.60  # System time              : 0.010 s
% 0.42/0.60  # Total time               : 0.262 s
% 0.42/0.60  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
