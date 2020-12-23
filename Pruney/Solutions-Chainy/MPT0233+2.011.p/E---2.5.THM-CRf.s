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
% DateTime   : Thu Dec  3 10:38:58 EST 2020

% Result     : Theorem 1.38s
% Output     : CNFRefutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 482 expanded)
%              Number of clauses        :   50 ( 177 expanded)
%              Number of leaves         :   23 ( 151 expanded)
%              Depth                    :   11
%              Number of atoms          :  163 ( 594 expanded)
%              Number of equality atoms :  115 ( 528 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
        & X1 != X3
        & X1 != X4 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(t18_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t12_zfmisc_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
          & X1 != X3
          & X1 != X4 ) ),
    inference(assume_negation,[status(cth)],[t28_zfmisc_1])).

fof(c_0_24,negated_conjecture,
    ( r1_tarski(k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))
    & esk2_0 != esk4_0
    & esk2_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_25,plain,(
    ! [X48,X49] : k1_enumset1(X48,X48,X49) = k2_tarski(X48,X49) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_26,plain,(
    ! [X50,X51,X52] : k2_enumset1(X50,X50,X51,X52) = k1_enumset1(X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X53,X54,X55,X56] : k3_enumset1(X53,X53,X54,X55,X56) = k2_enumset1(X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X57,X58,X59,X60,X61] : k4_enumset1(X57,X57,X58,X59,X60,X61) = k3_enumset1(X57,X58,X59,X60,X61) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_29,plain,(
    ! [X62,X63,X64,X65,X66,X67] : k5_enumset1(X62,X62,X63,X64,X65,X66,X67) = k4_enumset1(X62,X63,X64,X65,X66,X67) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_30,plain,(
    ! [X68,X69,X70,X71,X72,X73,X74] : k6_enumset1(X68,X68,X69,X70,X71,X72,X73,X74) = k5_enumset1(X68,X69,X70,X71,X72,X73,X74) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_31,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,k3_xboole_0(X18,X19))
      | r1_tarski(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).

fof(c_0_32,plain,(
    ! [X10,X11] : k3_xboole_0(X10,X11) = k3_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_33,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k3_xboole_0(X20,X21) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

fof(c_0_45,plain,(
    ! [X75,X76] : r1_tarski(k1_tarski(X75),k2_tarski(X75,X76)) ),
    inference(variable_rename,[status(thm)],[t12_zfmisc_1])).

fof(c_0_46,plain,(
    ! [X47] : k2_tarski(X47,X47) = k1_tarski(X47) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_47,plain,(
    ! [X22] :
      ( ~ r1_tarski(X22,k1_xboole_0)
      | X22 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_48,plain,(
    ! [X15,X16] : r1_tarski(k3_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_53,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_54,plain,(
    ! [X13,X14] : k4_xboole_0(X13,X14) = k5_xboole_0(X13,k3_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_57,plain,(
    ! [X28,X29,X30,X31,X32,X33,X34,X35,X36,X37] :
      ( ( ~ r2_hidden(X32,X31)
        | X32 = X28
        | X32 = X29
        | X32 = X30
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X28
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X29
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X30
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( esk1_4(X34,X35,X36,X37) != X34
        | ~ r2_hidden(esk1_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( esk1_4(X34,X35,X36,X37) != X35
        | ~ r2_hidden(esk1_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( esk1_4(X34,X35,X36,X37) != X36
        | ~ r2_hidden(esk1_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( r2_hidden(esk1_4(X34,X35,X36,X37),X37)
        | esk1_4(X34,X35,X36,X37) = X34
        | esk1_4(X34,X35,X36,X37) = X35
        | esk1_4(X34,X35,X36,X37) = X36
        | X37 = k1_enumset1(X34,X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_58,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_59,plain,(
    ! [X26,X27] : k2_xboole_0(X26,X27) = k5_xboole_0(X26,k4_xboole_0(X27,X26)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(X1,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))
    | ~ r1_tarski(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

fof(c_0_62,plain,(
    ! [X39,X40,X41,X42] : k2_enumset1(X39,X40,X41,X42) = k2_xboole_0(k1_tarski(X39),k1_enumset1(X40,X41,X42)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_66,plain,(
    ! [X25] : k5_xboole_0(X25,k1_xboole_0) = X25 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_67,plain,(
    ! [X12] : k3_xboole_0(X12,X12) = X12 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_69,plain,(
    ! [X43,X44,X45,X46] : k2_enumset1(X43,X44,X45,X46) = k2_xboole_0(k1_enumset1(X43,X44,X45),k1_tarski(X46)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_70,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_71,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_72,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_74,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_64])).

cnf(c_0_76,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_65])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_78,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_80,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_81,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_82,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72]),c_0_72]),c_0_64]),c_0_64])).

cnf(c_0_83,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_73])).

cnf(c_0_84,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_52]),c_0_35]),c_0_72]),c_0_64]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_78])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_79])).

cnf(c_0_87,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_52]),c_0_35]),c_0_72]),c_0_64]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_88,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk4_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_85]),c_0_77])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_86])).

cnf(c_0_91,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_87]),c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( X1 = esk4_0
    | X1 = esk5_0
    | ~ r2_hidden(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_93,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X2,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( esk2_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_95,negated_conjecture,
    ( esk2_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94]),c_0_95]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:55:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 1.38/1.57  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 1.38/1.57  # and selection function SelectNegativeLiterals.
% 1.38/1.57  #
% 1.38/1.57  # Preprocessing time       : 0.027 s
% 1.38/1.57  
% 1.38/1.57  # Proof found!
% 1.38/1.57  # SZS status Theorem
% 1.38/1.57  # SZS output start CNFRefutation
% 1.38/1.57  fof(t28_zfmisc_1, conjecture, ![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 1.38/1.57  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.38/1.57  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.38/1.57  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.38/1.57  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.38/1.57  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 1.38/1.57  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 1.38/1.57  fof(t18_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k3_xboole_0(X2,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 1.38/1.57  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.38/1.57  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.38/1.57  fof(t12_zfmisc_1, axiom, ![X1, X2]:r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.38/1.57  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.38/1.57  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.38/1.57  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.38/1.57  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.38/1.57  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.38/1.57  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 1.38/1.57  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.38/1.57  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.38/1.57  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 1.38/1.57  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 1.38/1.57  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.38/1.57  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 1.38/1.57  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4))), inference(assume_negation,[status(cth)],[t28_zfmisc_1])).
% 1.38/1.57  fof(c_0_24, negated_conjecture, ((r1_tarski(k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))&esk2_0!=esk4_0)&esk2_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 1.38/1.57  fof(c_0_25, plain, ![X48, X49]:k1_enumset1(X48,X48,X49)=k2_tarski(X48,X49), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.38/1.57  fof(c_0_26, plain, ![X50, X51, X52]:k2_enumset1(X50,X50,X51,X52)=k1_enumset1(X50,X51,X52), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.38/1.57  fof(c_0_27, plain, ![X53, X54, X55, X56]:k3_enumset1(X53,X53,X54,X55,X56)=k2_enumset1(X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.38/1.57  fof(c_0_28, plain, ![X57, X58, X59, X60, X61]:k4_enumset1(X57,X57,X58,X59,X60,X61)=k3_enumset1(X57,X58,X59,X60,X61), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 1.38/1.57  fof(c_0_29, plain, ![X62, X63, X64, X65, X66, X67]:k5_enumset1(X62,X62,X63,X64,X65,X66,X67)=k4_enumset1(X62,X63,X64,X65,X66,X67), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 1.38/1.57  fof(c_0_30, plain, ![X68, X69, X70, X71, X72, X73, X74]:k6_enumset1(X68,X68,X69,X70,X71,X72,X73,X74)=k5_enumset1(X68,X69,X70,X71,X72,X73,X74), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 1.38/1.57  fof(c_0_31, plain, ![X17, X18, X19]:(~r1_tarski(X17,k3_xboole_0(X18,X19))|r1_tarski(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).
% 1.38/1.57  fof(c_0_32, plain, ![X10, X11]:k3_xboole_0(X10,X11)=k3_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.38/1.57  fof(c_0_33, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k3_xboole_0(X20,X21)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 1.38/1.57  cnf(c_0_34, negated_conjecture, (r1_tarski(k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.38/1.57  cnf(c_0_35, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.38/1.57  cnf(c_0_36, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.38/1.57  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.38/1.57  cnf(c_0_38, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.38/1.57  cnf(c_0_39, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.38/1.57  cnf(c_0_40, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.38/1.57  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.38/1.57  cnf(c_0_42, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.38/1.57  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.38/1.57  cnf(c_0_44, negated_conjecture, (r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 1.38/1.57  fof(c_0_45, plain, ![X75, X76]:r1_tarski(k1_tarski(X75),k2_tarski(X75,X76)), inference(variable_rename,[status(thm)],[t12_zfmisc_1])).
% 1.38/1.57  fof(c_0_46, plain, ![X47]:k2_tarski(X47,X47)=k1_tarski(X47), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.38/1.57  fof(c_0_47, plain, ![X22]:(~r1_tarski(X22,k1_xboole_0)|X22=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 1.38/1.57  fof(c_0_48, plain, ![X15, X16]:r1_tarski(k3_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 1.38/1.57  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.38/1.57  cnf(c_0_50, negated_conjecture, (k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 1.38/1.57  cnf(c_0_51, plain, (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.38/1.57  cnf(c_0_52, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.38/1.57  fof(c_0_53, plain, ![X23, X24]:k4_xboole_0(X23,k4_xboole_0(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.38/1.57  fof(c_0_54, plain, ![X13, X14]:k4_xboole_0(X13,X14)=k5_xboole_0(X13,k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.38/1.57  cnf(c_0_55, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.38/1.57  cnf(c_0_56, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.38/1.57  fof(c_0_57, plain, ![X28, X29, X30, X31, X32, X33, X34, X35, X36, X37]:(((~r2_hidden(X32,X31)|(X32=X28|X32=X29|X32=X30)|X31!=k1_enumset1(X28,X29,X30))&(((X33!=X28|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30))&(X33!=X29|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30)))&(X33!=X30|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30))))&((((esk1_4(X34,X35,X36,X37)!=X34|~r2_hidden(esk1_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36))&(esk1_4(X34,X35,X36,X37)!=X35|~r2_hidden(esk1_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36)))&(esk1_4(X34,X35,X36,X37)!=X36|~r2_hidden(esk1_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36)))&(r2_hidden(esk1_4(X34,X35,X36,X37),X37)|(esk1_4(X34,X35,X36,X37)=X34|esk1_4(X34,X35,X36,X37)=X35|esk1_4(X34,X35,X36,X37)=X36)|X37=k1_enumset1(X34,X35,X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 1.38/1.57  fof(c_0_58, plain, ![X8, X9]:k2_xboole_0(X8,X9)=k2_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.38/1.57  fof(c_0_59, plain, ![X26, X27]:k2_xboole_0(X26,X27)=k5_xboole_0(X26,k4_xboole_0(X27,X26)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 1.38/1.57  cnf(c_0_60, negated_conjecture, (r1_tarski(X1,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))|~r1_tarski(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.38/1.57  cnf(c_0_61, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 1.38/1.57  fof(c_0_62, plain, ![X39, X40, X41, X42]:k2_enumset1(X39,X40,X41,X42)=k2_xboole_0(k1_tarski(X39),k1_enumset1(X40,X41,X42)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 1.38/1.57  cnf(c_0_63, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.38/1.57  cnf(c_0_64, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.38/1.57  cnf(c_0_65, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 1.38/1.57  fof(c_0_66, plain, ![X25]:k5_xboole_0(X25,k1_xboole_0)=X25, inference(variable_rename,[status(thm)],[t5_boole])).
% 1.38/1.57  fof(c_0_67, plain, ![X12]:k3_xboole_0(X12,X12)=X12, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 1.38/1.57  cnf(c_0_68, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.38/1.57  fof(c_0_69, plain, ![X43, X44, X45, X46]:k2_enumset1(X43,X44,X45,X46)=k2_xboole_0(k1_enumset1(X43,X44,X45),k1_tarski(X46)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 1.38/1.57  cnf(c_0_70, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.38/1.57  cnf(c_0_71, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.38/1.57  cnf(c_0_72, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 1.38/1.57  cnf(c_0_73, negated_conjecture, (r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 1.38/1.57  cnf(c_0_74, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.38/1.57  cnf(c_0_75, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64]), c_0_64])).
% 1.38/1.57  cnf(c_0_76, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_65])).
% 1.38/1.57  cnf(c_0_77, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_66])).
% 1.38/1.57  cnf(c_0_78, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_67])).
% 1.38/1.57  cnf(c_0_79, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 1.38/1.57  cnf(c_0_80, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 1.38/1.57  cnf(c_0_81, plain, (X1=X5|X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 1.38/1.57  cnf(c_0_82, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72]), c_0_72]), c_0_64]), c_0_64])).
% 1.38/1.57  cnf(c_0_83, negated_conjecture, (k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_73])).
% 1.38/1.57  cnf(c_0_84, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_52]), c_0_35]), c_0_72]), c_0_64]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 1.38/1.57  cnf(c_0_85, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_78])).
% 1.38/1.57  cnf(c_0_86, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_79])).
% 1.38/1.57  cnf(c_0_87, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_52]), c_0_35]), c_0_72]), c_0_64]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 1.38/1.57  cnf(c_0_88, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_81])).
% 1.38/1.57  cnf(c_0_89, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk4_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_85]), c_0_77])).
% 1.38/1.57  cnf(c_0_90, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[c_0_86])).
% 1.38/1.57  cnf(c_0_91, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_87]), c_0_84])).
% 1.38/1.57  cnf(c_0_92, negated_conjecture, (X1=esk4_0|X1=esk5_0|~r2_hidden(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 1.38/1.57  cnf(c_0_93, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X2,X2,X3))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 1.38/1.57  cnf(c_0_94, negated_conjecture, (esk2_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.38/1.57  cnf(c_0_95, negated_conjecture, (esk2_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.38/1.57  cnf(c_0_96, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94]), c_0_95]), ['proof']).
% 1.38/1.57  # SZS output end CNFRefutation
% 1.38/1.57  # Proof object total steps             : 97
% 1.38/1.57  # Proof object clause steps            : 50
% 1.38/1.57  # Proof object formula steps           : 47
% 1.38/1.57  # Proof object conjectures             : 14
% 1.38/1.57  # Proof object clause conjectures      : 11
% 1.38/1.57  # Proof object formula conjectures     : 3
% 1.38/1.57  # Proof object initial clauses used    : 26
% 1.38/1.57  # Proof object initial formulas used   : 23
% 1.38/1.57  # Proof object generating inferences   : 15
% 1.38/1.57  # Proof object simplifying inferences  : 106
% 1.38/1.57  # Training examples: 0 positive, 0 negative
% 1.38/1.57  # Parsed axioms                        : 23
% 1.38/1.57  # Removed by relevancy pruning/SinE    : 0
% 1.38/1.57  # Initial clauses                      : 32
% 1.38/1.57  # Removed in clause preprocessing      : 9
% 1.38/1.57  # Initial clauses in saturation        : 23
% 1.38/1.57  # Processed clauses                    : 2823
% 1.38/1.57  # ...of these trivial                  : 355
% 1.38/1.57  # ...subsumed                          : 1950
% 1.38/1.57  # ...remaining for further processing  : 518
% 1.38/1.57  # Other redundant clauses eliminated   : 207
% 1.38/1.57  # Clauses deleted for lack of memory   : 0
% 1.38/1.57  # Backward-subsumed                    : 2
% 1.38/1.57  # Backward-rewritten                   : 6
% 1.38/1.57  # Generated clauses                    : 61352
% 1.38/1.57  # ...of the previous two non-trivial   : 54235
% 1.38/1.57  # Contextual simplify-reflections      : 0
% 1.38/1.57  # Paramodulations                      : 61092
% 1.38/1.57  # Factorizations                       : 28
% 1.38/1.57  # Equation resolutions                 : 232
% 1.38/1.57  # Propositional unsat checks           : 0
% 1.38/1.57  #    Propositional check models        : 0
% 1.38/1.57  #    Propositional check unsatisfiable : 0
% 1.38/1.57  #    Propositional clauses             : 0
% 1.38/1.57  #    Propositional clauses after purity: 0
% 1.38/1.57  #    Propositional unsat core size     : 0
% 1.38/1.57  #    Propositional preprocessing time  : 0.000
% 1.38/1.57  #    Propositional encoding time       : 0.000
% 1.38/1.57  #    Propositional solver time         : 0.000
% 1.38/1.57  #    Success case prop preproc time    : 0.000
% 1.38/1.57  #    Success case prop encoding time   : 0.000
% 1.38/1.57  #    Success case prop solver time     : 0.000
% 1.38/1.57  # Current number of processed clauses  : 507
% 1.38/1.57  #    Positive orientable unit clauses  : 209
% 1.38/1.57  #    Positive unorientable unit clauses: 5
% 1.38/1.57  #    Negative unit clauses             : 2
% 1.38/1.57  #    Non-unit-clauses                  : 291
% 1.38/1.57  # Current number of unprocessed clauses: 51390
% 1.38/1.57  # ...number of literals in the above   : 284785
% 1.38/1.57  # Current number of archived formulas  : 0
% 1.38/1.57  # Current number of archived clauses   : 17
% 1.38/1.57  # Clause-clause subsumption calls (NU) : 54474
% 1.38/1.57  # Rec. Clause-clause subsumption calls : 44952
% 1.38/1.57  # Non-unit clause-clause subsumptions  : 1940
% 1.38/1.57  # Unit Clause-clause subsumption calls : 1989
% 1.38/1.57  # Rewrite failures with RHS unbound    : 0
% 1.38/1.57  # BW rewrite match attempts            : 1647
% 1.38/1.57  # BW rewrite match successes           : 69
% 1.38/1.57  # Condensation attempts                : 0
% 1.38/1.57  # Condensation successes               : 0
% 1.38/1.57  # Termbank termtop insertions          : 1836006
% 1.38/1.58  
% 1.38/1.58  # -------------------------------------------------
% 1.38/1.58  # User time                : 1.200 s
% 1.38/1.58  # System time              : 0.032 s
% 1.38/1.58  # Total time               : 1.231 s
% 1.38/1.58  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
