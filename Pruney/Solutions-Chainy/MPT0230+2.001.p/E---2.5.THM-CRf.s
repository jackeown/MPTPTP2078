%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:30 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 197 expanded)
%              Number of clauses        :   39 (  82 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  138 ( 318 expanded)
%              Number of equality atoms :  102 ( 249 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t25_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))
        & X1 != X2
        & X1 != X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_16,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k3_xboole_0(X14,X15) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_17,plain,(
    ! [X16] : r1_tarski(k1_xboole_0,X16) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))
          & X1 != X2
          & X1 != X3 ) ),
    inference(assume_negation,[status(cth)],[t25_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X17] : k4_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_20,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_25,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_26,plain,(
    ! [X20,X21] : k2_xboole_0(X20,X21) = k5_xboole_0(X20,k4_xboole_0(X21,X20)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_27,plain,(
    ! [X33,X34,X35] : k1_enumset1(X33,X34,X35) = k2_xboole_0(k1_tarski(X33),k2_tarski(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_28,plain,(
    ! [X36] : k2_tarski(X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_29,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_30,plain,(
    ! [X39,X40,X41] : k2_enumset1(X39,X39,X40,X41) = k1_enumset1(X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_31,plain,(
    ! [X42,X43,X44,X45] : k3_enumset1(X42,X42,X43,X44,X45) = k2_enumset1(X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_32,negated_conjecture,
    ( r1_tarski(k1_tarski(esk2_0),k2_tarski(esk3_0,esk4_0))
    & esk2_0 != esk3_0
    & esk2_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_33,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k3_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_39,plain,(
    ! [X22,X23,X24,X25,X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X26,X25)
        | X26 = X22
        | X26 = X23
        | X26 = X24
        | X25 != k1_enumset1(X22,X23,X24) )
      & ( X27 != X22
        | r2_hidden(X27,X25)
        | X25 != k1_enumset1(X22,X23,X24) )
      & ( X27 != X23
        | r2_hidden(X27,X25)
        | X25 != k1_enumset1(X22,X23,X24) )
      & ( X27 != X24
        | r2_hidden(X27,X25)
        | X25 != k1_enumset1(X22,X23,X24) )
      & ( esk1_4(X28,X29,X30,X31) != X28
        | ~ r2_hidden(esk1_4(X28,X29,X30,X31),X31)
        | X31 = k1_enumset1(X28,X29,X30) )
      & ( esk1_4(X28,X29,X30,X31) != X29
        | ~ r2_hidden(esk1_4(X28,X29,X30,X31),X31)
        | X31 = k1_enumset1(X28,X29,X30) )
      & ( esk1_4(X28,X29,X30,X31) != X30
        | ~ r2_hidden(esk1_4(X28,X29,X30,X31),X31)
        | X31 = k1_enumset1(X28,X29,X30) )
      & ( r2_hidden(esk1_4(X28,X29,X30,X31),X31)
        | esk1_4(X28,X29,X30,X31) = X28
        | esk1_4(X28,X29,X30,X31) = X29
        | esk1_4(X28,X29,X30,X31) = X30
        | X31 = k1_enumset1(X28,X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_tarski(esk2_0),k2_tarski(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_41]),c_0_35]),c_0_35])).

cnf(c_0_54,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X3),k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X3),k3_enumset1(X1,X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_44]),c_0_41]),c_0_35]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_35]),c_0_35])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_22,c_0_51])).

cnf(c_0_59,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_45]),c_0_46])).

cnf(c_0_60,plain,
    ( k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X1,X1,X1,X1,X2)))) = k3_enumset1(X3,X3,X3,X1,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_55])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_50]),c_0_57]),c_0_58])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_64,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k3_enumset1(esk2_0,esk2_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_57])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_45]),c_0_46])).

cnf(c_0_67,negated_conjecture,
    ( X1 = esk4_0
    | X1 = esk3_0
    | ~ r2_hidden(X1,k3_enumset1(esk2_0,esk2_0,esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_66])])).

cnf(c_0_69,negated_conjecture,
    ( esk2_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_70,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:15:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.13/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.38  fof(t25_zfmisc_1, conjecture, ![X1, X2, X3]:~(((r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))&X1!=X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 0.13/0.38  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.13/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.13/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.13/0.38  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.38  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.13/0.38  fof(c_0_16, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k3_xboole_0(X14,X15)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.13/0.38  fof(c_0_17, plain, ![X16]:r1_tarski(k1_xboole_0,X16), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.38  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:~(((r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))&X1!=X2)&X1!=X3))), inference(assume_negation,[status(cth)],[t25_zfmisc_1])).
% 0.13/0.38  fof(c_0_19, plain, ![X17]:k4_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.13/0.38  fof(c_0_20, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.38  fof(c_0_21, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.38  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_23, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  fof(c_0_24, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  fof(c_0_25, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k2_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.13/0.38  fof(c_0_26, plain, ![X20, X21]:k2_xboole_0(X20,X21)=k5_xboole_0(X20,k4_xboole_0(X21,X20)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.13/0.38  fof(c_0_27, plain, ![X33, X34, X35]:k1_enumset1(X33,X34,X35)=k2_xboole_0(k1_tarski(X33),k2_tarski(X34,X35)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.13/0.38  fof(c_0_28, plain, ![X36]:k2_tarski(X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_29, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_30, plain, ![X39, X40, X41]:k2_enumset1(X39,X39,X40,X41)=k1_enumset1(X39,X40,X41), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_31, plain, ![X42, X43, X44, X45]:k3_enumset1(X42,X42,X43,X44,X45)=k2_enumset1(X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.38  fof(c_0_32, negated_conjecture, ((r1_tarski(k1_tarski(esk2_0),k2_tarski(esk3_0,esk4_0))&esk2_0!=esk3_0)&esk2_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.13/0.38  fof(c_0_33, plain, ![X18, X19]:k4_xboole_0(X18,k4_xboole_0(X18,X19))=k3_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.38  cnf(c_0_34, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_35, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_37, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.38  cnf(c_0_38, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  fof(c_0_39, plain, ![X22, X23, X24, X25, X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X26,X25)|(X26=X22|X26=X23|X26=X24)|X25!=k1_enumset1(X22,X23,X24))&(((X27!=X22|r2_hidden(X27,X25)|X25!=k1_enumset1(X22,X23,X24))&(X27!=X23|r2_hidden(X27,X25)|X25!=k1_enumset1(X22,X23,X24)))&(X27!=X24|r2_hidden(X27,X25)|X25!=k1_enumset1(X22,X23,X24))))&((((esk1_4(X28,X29,X30,X31)!=X28|~r2_hidden(esk1_4(X28,X29,X30,X31),X31)|X31=k1_enumset1(X28,X29,X30))&(esk1_4(X28,X29,X30,X31)!=X29|~r2_hidden(esk1_4(X28,X29,X30,X31),X31)|X31=k1_enumset1(X28,X29,X30)))&(esk1_4(X28,X29,X30,X31)!=X30|~r2_hidden(esk1_4(X28,X29,X30,X31),X31)|X31=k1_enumset1(X28,X29,X30)))&(r2_hidden(esk1_4(X28,X29,X30,X31),X31)|(esk1_4(X28,X29,X30,X31)=X28|esk1_4(X28,X29,X30,X31)=X29|esk1_4(X28,X29,X30,X31)=X30)|X31=k1_enumset1(X28,X29,X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.13/0.38  cnf(c_0_40, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_41, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_42, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_43, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_44, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_45, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_46, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_tarski(esk2_0),k2_tarski(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_49, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.38  cnf(c_0_50, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.38  cnf(c_0_51, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_38])).
% 0.13/0.38  cnf(c_0_52, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_53, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_41]), c_0_35]), c_0_35])).
% 0.13/0.38  cnf(c_0_54, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X3),k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X3),k3_enumset1(X1,X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_44]), c_0_41]), c_0_35]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46])).
% 0.13/0.38  cnf(c_0_56, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_35]), c_0_35])).
% 0.13/0.38  cnf(c_0_57, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.38  cnf(c_0_58, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_22, c_0_51])).
% 0.13/0.38  cnf(c_0_59, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_45]), c_0_46])).
% 0.13/0.38  cnf(c_0_60, plain, (k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X1,X1,X1,X1,X2))))=k3_enumset1(X3,X3,X3,X1,X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_22, c_0_55])).
% 0.13/0.38  cnf(c_0_62, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_50]), c_0_57]), c_0_58])).
% 0.13/0.38  cnf(c_0_63, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_64, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_59])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k3_enumset1(esk2_0,esk2_0,esk2_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_57])).
% 0.13/0.38  cnf(c_0_66, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_45]), c_0_46])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (X1=esk4_0|X1=esk3_0|~r2_hidden(X1,k3_enumset1(esk2_0,esk2_0,esk2_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.13/0.38  cnf(c_0_68, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_66])])).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (esk2_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_70]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 72
% 0.13/0.38  # Proof object clause steps            : 39
% 0.13/0.38  # Proof object formula steps           : 33
% 0.13/0.38  # Proof object conjectures             : 11
% 0.13/0.38  # Proof object clause conjectures      : 8
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 19
% 0.13/0.38  # Proof object initial formulas used   : 16
% 0.13/0.38  # Proof object generating inferences   : 9
% 0.13/0.38  # Proof object simplifying inferences  : 44
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 16
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 27
% 0.13/0.38  # Removed in clause preprocessing      : 6
% 0.13/0.38  # Initial clauses in saturation        : 21
% 0.13/0.38  # Processed clauses                    : 102
% 0.13/0.38  # ...of these trivial                  : 20
% 0.13/0.38  # ...subsumed                          : 7
% 0.13/0.38  # ...remaining for further processing  : 75
% 0.13/0.38  # Other redundant clauses eliminated   : 9
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 13
% 0.13/0.38  # Generated clauses                    : 234
% 0.13/0.38  # ...of the previous two non-trivial   : 143
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 228
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 9
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 36
% 0.13/0.38  #    Positive orientable unit clauses  : 20
% 0.13/0.38  #    Positive unorientable unit clauses: 5
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 9
% 0.13/0.38  # Current number of unprocessed clauses: 69
% 0.13/0.38  # ...number of literals in the above   : 83
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 39
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 16
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 16
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 11
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 72
% 0.13/0.38  # BW rewrite match successes           : 34
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 5250
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.032 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.036 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
