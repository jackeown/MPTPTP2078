%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:47 EST 2020

% Result     : Theorem 1.08s
% Output     : CNFRefutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 437 expanded)
%              Number of clauses        :   36 ( 159 expanded)
%              Number of leaves         :   16 ( 138 expanded)
%              Depth                    :    9
%              Number of atoms          :  125 ( 527 expanded)
%              Number of equality atoms :   99 ( 492 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t18_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(c_0_16,plain,(
    ! [X14,X15] : r1_tarski(k3_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_17,plain,(
    ! [X16,X17] : k3_xboole_0(X16,X17) = k5_xboole_0(k5_xboole_0(X16,X17),k2_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_18,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k2_xboole_0(X12,X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_19,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_22,plain,(
    ! [X10,X11] : k3_xboole_0(X10,X11) = k3_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t18_zfmisc_1])).

fof(c_0_24,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27,X28,X29] :
      ( ( ~ r2_hidden(X24,X23)
        | X24 = X20
        | X24 = X21
        | X24 = X22
        | X23 != k1_enumset1(X20,X21,X22) )
      & ( X25 != X20
        | r2_hidden(X25,X23)
        | X23 != k1_enumset1(X20,X21,X22) )
      & ( X25 != X21
        | r2_hidden(X25,X23)
        | X23 != k1_enumset1(X20,X21,X22) )
      & ( X25 != X22
        | r2_hidden(X25,X23)
        | X23 != k1_enumset1(X20,X21,X22) )
      & ( esk1_4(X26,X27,X28,X29) != X26
        | ~ r2_hidden(esk1_4(X26,X27,X28,X29),X29)
        | X29 = k1_enumset1(X26,X27,X28) )
      & ( esk1_4(X26,X27,X28,X29) != X27
        | ~ r2_hidden(esk1_4(X26,X27,X28,X29),X29)
        | X29 = k1_enumset1(X26,X27,X28) )
      & ( esk1_4(X26,X27,X28,X29) != X28
        | ~ r2_hidden(esk1_4(X26,X27,X28,X29),X29)
        | X29 = k1_enumset1(X26,X27,X28) )
      & ( r2_hidden(esk1_4(X26,X27,X28,X29),X29)
        | esk1_4(X26,X27,X28,X29) = X26
        | esk1_4(X26,X27,X28,X29) = X27
        | esk1_4(X26,X27,X28,X29) = X28
        | X29 = k1_enumset1(X26,X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_25,plain,(
    ! [X36,X37,X38] : k2_enumset1(X36,X36,X37,X38) = k1_enumset1(X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X39,X40,X41,X42] : k3_enumset1(X39,X39,X40,X41,X42) = k2_enumset1(X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X43,X44,X45,X46,X47] : k4_enumset1(X43,X43,X44,X45,X46,X47) = k3_enumset1(X43,X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_28,plain,(
    ! [X48,X49,X50,X51,X52,X53] : k5_enumset1(X48,X48,X49,X50,X51,X52,X53) = k4_enumset1(X48,X49,X50,X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_29,plain,(
    ! [X54,X55,X56,X57,X58,X59,X60] : k6_enumset1(X54,X54,X55,X56,X57,X58,X59,X60) = k5_enumset1(X54,X55,X56,X57,X58,X59,X60) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_30,plain,(
    ! [X18,X19] : k2_tarski(X18,X19) = k2_tarski(X19,X18) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_31,plain,(
    ! [X34,X35] : k1_enumset1(X34,X34,X35) = k2_tarski(X34,X35) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_36,plain,(
    ! [X31,X32] : k2_tarski(X31,X32) = k2_xboole_0(k1_tarski(X31),k1_tarski(X32)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_37,plain,(
    ! [X33] : k2_tarski(X33,X33) = k1_tarski(X33) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_38,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_39,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_20]),c_0_20])).

cnf(c_0_49,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_46]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_50]),c_0_46]),c_0_46]),c_0_46]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k2_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_50]),c_0_50]),c_0_50]),c_0_46]),c_0_46]),c_0_46]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_20]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_58,plain,
    ( X1 = X2
    | X1 = X3
    | X4 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_62,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_55]),c_0_53])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( X1 = esk3_0
    | ~ r2_hidden(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:14:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 1.08/1.25  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 1.08/1.25  # and selection function SelectNegativeLiterals.
% 1.08/1.25  #
% 1.08/1.25  # Preprocessing time       : 0.027 s
% 1.08/1.25  
% 1.08/1.25  # Proof found!
% 1.08/1.25  # SZS status Theorem
% 1.08/1.25  # SZS output start CNFRefutation
% 1.08/1.25  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.08/1.25  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 1.08/1.25  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.08/1.25  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.08/1.25  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.08/1.25  fof(t18_zfmisc_1, conjecture, ![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.08/1.25  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 1.08/1.25  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.08/1.25  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.08/1.25  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.08/1.25  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 1.08/1.25  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 1.08/1.25  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.08/1.25  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.08/1.25  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.08/1.25  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.08/1.25  fof(c_0_16, plain, ![X14, X15]:r1_tarski(k3_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 1.08/1.25  fof(c_0_17, plain, ![X16, X17]:k3_xboole_0(X16,X17)=k5_xboole_0(k5_xboole_0(X16,X17),k2_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 1.08/1.25  fof(c_0_18, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k2_xboole_0(X12,X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 1.08/1.25  cnf(c_0_19, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.08/1.25  cnf(c_0_20, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.08/1.25  fof(c_0_21, plain, ![X8, X9]:k2_xboole_0(X8,X9)=k2_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.08/1.25  fof(c_0_22, plain, ![X10, X11]:k3_xboole_0(X10,X11)=k3_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.08/1.25  fof(c_0_23, negated_conjecture, ~(![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t18_zfmisc_1])).
% 1.08/1.25  fof(c_0_24, plain, ![X20, X21, X22, X23, X24, X25, X26, X27, X28, X29]:(((~r2_hidden(X24,X23)|(X24=X20|X24=X21|X24=X22)|X23!=k1_enumset1(X20,X21,X22))&(((X25!=X20|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22))&(X25!=X21|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22)))&(X25!=X22|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22))))&((((esk1_4(X26,X27,X28,X29)!=X26|~r2_hidden(esk1_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28))&(esk1_4(X26,X27,X28,X29)!=X27|~r2_hidden(esk1_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28)))&(esk1_4(X26,X27,X28,X29)!=X28|~r2_hidden(esk1_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28)))&(r2_hidden(esk1_4(X26,X27,X28,X29),X29)|(esk1_4(X26,X27,X28,X29)=X26|esk1_4(X26,X27,X28,X29)=X27|esk1_4(X26,X27,X28,X29)=X28)|X29=k1_enumset1(X26,X27,X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 1.08/1.25  fof(c_0_25, plain, ![X36, X37, X38]:k2_enumset1(X36,X36,X37,X38)=k1_enumset1(X36,X37,X38), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.08/1.25  fof(c_0_26, plain, ![X39, X40, X41, X42]:k3_enumset1(X39,X39,X40,X41,X42)=k2_enumset1(X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.08/1.25  fof(c_0_27, plain, ![X43, X44, X45, X46, X47]:k4_enumset1(X43,X43,X44,X45,X46,X47)=k3_enumset1(X43,X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 1.08/1.25  fof(c_0_28, plain, ![X48, X49, X50, X51, X52, X53]:k5_enumset1(X48,X48,X49,X50,X51,X52,X53)=k4_enumset1(X48,X49,X50,X51,X52,X53), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 1.08/1.25  fof(c_0_29, plain, ![X54, X55, X56, X57, X58, X59, X60]:k6_enumset1(X54,X54,X55,X56,X57,X58,X59,X60)=k5_enumset1(X54,X55,X56,X57,X58,X59,X60), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 1.08/1.25  fof(c_0_30, plain, ![X18, X19]:k2_tarski(X18,X19)=k2_tarski(X19,X18), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.08/1.25  fof(c_0_31, plain, ![X34, X35]:k1_enumset1(X34,X34,X35)=k2_tarski(X34,X35), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.08/1.25  cnf(c_0_32, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.08/1.25  cnf(c_0_33, plain, (r1_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 1.08/1.25  cnf(c_0_34, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.08/1.25  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.08/1.25  fof(c_0_36, plain, ![X31, X32]:k2_tarski(X31,X32)=k2_xboole_0(k1_tarski(X31),k1_tarski(X32)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 1.08/1.25  fof(c_0_37, plain, ![X33]:k2_tarski(X33,X33)=k1_tarski(X33), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.08/1.25  fof(c_0_38, negated_conjecture, (k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)&esk2_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 1.08/1.25  cnf(c_0_39, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.08/1.25  cnf(c_0_40, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.08/1.25  cnf(c_0_41, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.08/1.25  cnf(c_0_42, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.08/1.25  cnf(c_0_43, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.08/1.25  cnf(c_0_44, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.08/1.25  cnf(c_0_45, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.08/1.25  cnf(c_0_46, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.08/1.25  cnf(c_0_47, plain, (k2_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 1.08/1.25  cnf(c_0_48, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_20]), c_0_20])).
% 1.08/1.25  cnf(c_0_49, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.08/1.25  cnf(c_0_50, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.08/1.25  cnf(c_0_51, negated_conjecture, (k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.08/1.25  cnf(c_0_52, plain, (X1=X5|X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 1.08/1.25  cnf(c_0_53, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_46]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44])).
% 1.08/1.25  cnf(c_0_54, plain, (k2_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)))=X1), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 1.08/1.25  cnf(c_0_55, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_50]), c_0_46]), c_0_46]), c_0_46]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44])).
% 1.08/1.25  cnf(c_0_56, negated_conjecture, (k5_xboole_0(k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k2_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_50]), c_0_50]), c_0_50]), c_0_46]), c_0_46]), c_0_46]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_20]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44])).
% 1.08/1.25  cnf(c_0_57, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.08/1.25  cnf(c_0_58, plain, (X1=X2|X1=X3|X4!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.08/1.25  cnf(c_0_59, plain, (k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 1.08/1.25  cnf(c_0_60, negated_conjecture, (k5_xboole_0(k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_56, c_0_55])).
% 1.08/1.25  cnf(c_0_61, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 1.08/1.25  cnf(c_0_62, plain, (X1=X2|X1=X3|~r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_58])).
% 1.08/1.25  cnf(c_0_63, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_55]), c_0_53])).
% 1.08/1.25  cnf(c_0_64, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4)), inference(er,[status(thm)],[c_0_61])).
% 1.08/1.25  cnf(c_0_65, negated_conjecture, (X1=esk3_0|~r2_hidden(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 1.08/1.25  cnf(c_0_66, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3))), inference(er,[status(thm)],[c_0_64])).
% 1.08/1.25  cnf(c_0_67, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.08/1.25  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), ['proof']).
% 1.08/1.25  # SZS output end CNFRefutation
% 1.08/1.25  # Proof object total steps             : 69
% 1.08/1.25  # Proof object clause steps            : 36
% 1.08/1.25  # Proof object formula steps           : 33
% 1.08/1.25  # Proof object conjectures             : 10
% 1.08/1.25  # Proof object clause conjectures      : 7
% 1.08/1.25  # Proof object formula conjectures     : 3
% 1.08/1.25  # Proof object initial clauses used    : 18
% 1.08/1.25  # Proof object initial formulas used   : 16
% 1.08/1.25  # Proof object generating inferences   : 9
% 1.08/1.25  # Proof object simplifying inferences  : 79
% 1.08/1.25  # Training examples: 0 positive, 0 negative
% 1.08/1.25  # Parsed axioms                        : 16
% 1.08/1.25  # Removed by relevancy pruning/SinE    : 0
% 1.08/1.25  # Initial clauses                      : 24
% 1.08/1.25  # Removed in clause preprocessing      : 8
% 1.08/1.25  # Initial clauses in saturation        : 16
% 1.08/1.25  # Processed clauses                    : 756
% 1.08/1.25  # ...of these trivial                  : 282
% 1.08/1.25  # ...subsumed                          : 233
% 1.08/1.25  # ...remaining for further processing  : 241
% 1.08/1.25  # Other redundant clauses eliminated   : 212
% 1.08/1.25  # Clauses deleted for lack of memory   : 0
% 1.08/1.25  # Backward-subsumed                    : 0
% 1.08/1.25  # Backward-rewritten                   : 70
% 1.08/1.25  # Generated clauses                    : 30900
% 1.08/1.25  # ...of the previous two non-trivial   : 29155
% 1.08/1.25  # Contextual simplify-reflections      : 5
% 1.08/1.25  # Paramodulations                      : 30630
% 1.08/1.25  # Factorizations                       : 29
% 1.08/1.25  # Equation resolutions                 : 241
% 1.08/1.25  # Propositional unsat checks           : 0
% 1.08/1.25  #    Propositional check models        : 0
% 1.08/1.25  #    Propositional check unsatisfiable : 0
% 1.08/1.25  #    Propositional clauses             : 0
% 1.08/1.25  #    Propositional clauses after purity: 0
% 1.08/1.25  #    Propositional unsat core size     : 0
% 1.08/1.25  #    Propositional preprocessing time  : 0.000
% 1.08/1.25  #    Propositional encoding time       : 0.000
% 1.08/1.25  #    Propositional solver time         : 0.000
% 1.08/1.25  #    Success case prop preproc time    : 0.000
% 1.08/1.25  #    Success case prop encoding time   : 0.000
% 1.08/1.25  #    Success case prop solver time     : 0.000
% 1.08/1.25  # Current number of processed clauses  : 168
% 1.08/1.25  #    Positive orientable unit clauses  : 89
% 1.08/1.25  #    Positive unorientable unit clauses: 5
% 1.08/1.25  #    Negative unit clauses             : 1
% 1.08/1.25  #    Non-unit-clauses                  : 73
% 1.08/1.25  # Current number of unprocessed clauses: 28252
% 1.08/1.25  # ...number of literals in the above   : 160480
% 1.08/1.25  # Current number of archived formulas  : 0
% 1.08/1.25  # Current number of archived clauses   : 78
% 1.08/1.25  # Clause-clause subsumption calls (NU) : 2767
% 1.08/1.25  # Rec. Clause-clause subsumption calls : 901
% 1.08/1.25  # Non-unit clause-clause subsumptions  : 228
% 1.08/1.25  # Unit Clause-clause subsumption calls : 107
% 1.08/1.25  # Rewrite failures with RHS unbound    : 0
% 1.08/1.25  # BW rewrite match attempts            : 2009
% 1.08/1.25  # BW rewrite match successes           : 25
% 1.08/1.25  # Condensation attempts                : 0
% 1.08/1.25  # Condensation successes               : 0
% 1.08/1.25  # Termbank termtop insertions          : 1913394
% 1.08/1.25  
% 1.08/1.25  # -------------------------------------------------
% 1.08/1.25  # User time                : 0.884 s
% 1.08/1.25  # System time              : 0.022 s
% 1.08/1.25  # Total time               : 0.906 s
% 1.08/1.25  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
