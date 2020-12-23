%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:02 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   80 (6880 expanded)
%              Number of clauses        :   53 (2824 expanded)
%              Number of leaves         :   13 (1992 expanded)
%              Depth                    :   19
%              Number of atoms          :  160 (8141 expanded)
%              Number of equality atoms :  107 (7730 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t44_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & X2 != X3
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_13,plain,(
    ! [X48,X49] : k3_tarski(k2_tarski(X48,X49)) = k2_xboole_0(X48,X49) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X39,X40] : k1_enumset1(X39,X39,X40) = k2_tarski(X39,X40) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X29,X30] : k4_xboole_0(X29,k2_xboole_0(X29,X30)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_16,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X24,X25] : k4_xboole_0(X24,X25) = k5_xboole_0(X24,k3_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_19,plain,(
    ! [X41,X42,X43] : k2_enumset1(X41,X41,X42,X43) = k1_enumset1(X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X44,X45,X46,X47] : k3_enumset1(X44,X44,X45,X46,X47) = k2_enumset1(X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,plain,(
    ! [X26] : k2_xboole_0(X26,k1_xboole_0) = X26 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_22,plain,(
    ! [X27,X28] : k2_xboole_0(X27,k4_xboole_0(X28,X27)) = k2_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & X2 != X3
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t44_zfmisc_1])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_32,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_24]),c_0_26]),c_0_27])).

fof(c_0_33,negated_conjecture,
    ( k1_tarski(esk5_0) = k2_xboole_0(esk6_0,esk7_0)
    & esk6_0 != esk7_0
    & esk6_0 != k1_xboole_0
    & esk7_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

fof(c_0_34,plain,(
    ! [X38] : k2_tarski(X38,X38) = k1_tarski(X38) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_35,plain,(
    ! [X31,X32,X33,X34,X35,X36] :
      ( ( ~ r2_hidden(X33,X32)
        | X33 = X31
        | X32 != k1_tarski(X31) )
      & ( X34 != X31
        | r2_hidden(X34,X32)
        | X32 != k1_tarski(X31) )
      & ( ~ r2_hidden(esk4_2(X35,X36),X36)
        | esk4_2(X35,X36) != X35
        | X36 = k1_tarski(X35) )
      & ( r2_hidden(esk4_2(X35,X36),X36)
        | esk4_2(X35,X36) = X35
        | X36 = k1_tarski(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_36,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_24]),c_0_24]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( k1_tarski(esk5_0) = k2_xboole_0(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_17]),c_0_24]),c_0_26]),c_0_26]),c_0_27]),c_0_27])).

fof(c_0_43,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X18)
        | r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k2_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_44,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_39]),c_0_17]),c_0_26]),c_0_27])).

cnf(c_0_45,negated_conjecture,
    ( esk5_0 = k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( k3_enumset1(k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))),k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))),k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))),k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))),k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)))) = k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k3_enumset1(X2,X2,X2,X2,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_24]),c_0_26]),c_0_27])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k3_enumset1(X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_24]),c_0_26]),c_0_27])).

cnf(c_0_52,negated_conjecture,
    ( X1 = k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)))
    | ~ r2_hidden(X1,k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_50])).

fof(c_0_54,plain,(
    ! [X20] :
      ( X20 = k1_xboole_0
      | r2_hidden(esk3_1(X20),X20) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( X1 = k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_59,negated_conjecture,
    ( X1 = k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))) = esk3_1(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_61,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | esk4_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_62,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_63,negated_conjecture,
    ( X1 = esk3_1(esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,plain,
    ( esk4_2(X1,X2) = X1
    | X2 = k3_enumset1(X1,X1,X1,X1,X1)
    | r2_hidden(esk4_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_39]),c_0_17]),c_0_26]),c_0_27])).

cnf(c_0_65,negated_conjecture,
    ( esk3_1(esk7_0) = k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_57]),c_0_62])).

cnf(c_0_66,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk4_2(X1,X2),X2)
    | esk4_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_67,negated_conjecture,
    ( esk7_0 = k3_enumset1(X1,X1,X1,X1,X1)
    | esk4_2(X1,esk7_0) = esk3_1(esk6_0)
    | esk4_2(X1,esk7_0) = X1 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_65]),c_0_62])).

cnf(c_0_69,plain,
    ( X2 = k3_enumset1(X1,X1,X1,X1,X1)
    | esk4_2(X1,X2) != X1
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_39]),c_0_17]),c_0_26]),c_0_27])).

cnf(c_0_70,negated_conjecture,
    ( esk7_0 = k3_enumset1(esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0))
    | esk4_2(esk3_1(esk6_0),esk7_0) = esk3_1(esk6_0) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_67])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_68,c_0_60])).

cnf(c_0_72,negated_conjecture,
    ( X1 = esk3_1(esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[c_0_56,c_0_60])).

cnf(c_0_73,negated_conjecture,
    ( esk6_0 != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_74,negated_conjecture,
    ( esk7_0 = k3_enumset1(esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_75,negated_conjecture,
    ( esk6_0 = k3_enumset1(X1,X1,X1,X1,X1)
    | esk4_2(X1,esk6_0) = esk3_1(esk6_0)
    | esk4_2(X1,esk6_0) = X1 ),
    inference(spm,[status(thm)],[c_0_72,c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( k3_enumset1(esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0)) != esk6_0 ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( esk4_2(esk3_1(esk6_0),esk6_0) = esk3_1(esk6_0) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_75])]),c_0_76])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_hidden(esk3_1(esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_77]),c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_57]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:02:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.14/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.38  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.14/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.14/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.14/0.38  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.14/0.38  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.14/0.38  fof(t44_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&X2!=X3)&X2!=k1_xboole_0)&X3!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 0.14/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.14/0.38  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.14/0.38  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.14/0.38  fof(c_0_13, plain, ![X48, X49]:k3_tarski(k2_tarski(X48,X49))=k2_xboole_0(X48,X49), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.14/0.38  fof(c_0_14, plain, ![X39, X40]:k1_enumset1(X39,X39,X40)=k2_tarski(X39,X40), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.38  fof(c_0_15, plain, ![X29, X30]:k4_xboole_0(X29,k2_xboole_0(X29,X30))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.14/0.38  cnf(c_0_16, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  fof(c_0_18, plain, ![X24, X25]:k4_xboole_0(X24,X25)=k5_xboole_0(X24,k3_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.14/0.38  fof(c_0_19, plain, ![X41, X42, X43]:k2_enumset1(X41,X41,X42,X43)=k1_enumset1(X41,X42,X43), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.38  fof(c_0_20, plain, ![X44, X45, X46, X47]:k3_enumset1(X44,X44,X45,X46,X47)=k2_enumset1(X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.14/0.38  fof(c_0_21, plain, ![X26]:k2_xboole_0(X26,k1_xboole_0)=X26, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.14/0.38  fof(c_0_22, plain, ![X27, X28]:k2_xboole_0(X27,k4_xboole_0(X28,X27))=k2_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.14/0.38  cnf(c_0_23, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_24, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.38  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_27, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_28, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  fof(c_0_29, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&X2!=X3)&X2!=k1_xboole_0)&X3!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t44_zfmisc_1])).
% 0.14/0.38  cnf(c_0_30, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_31, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27])).
% 0.14/0.38  cnf(c_0_32, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_24]), c_0_26]), c_0_27])).
% 0.14/0.38  fof(c_0_33, negated_conjecture, (((k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)&esk6_0!=esk7_0)&esk6_0!=k1_xboole_0)&esk7_0!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.14/0.38  fof(c_0_34, plain, ![X38]:k2_tarski(X38,X38)=k1_tarski(X38), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.38  fof(c_0_35, plain, ![X31, X32, X33, X34, X35, X36]:(((~r2_hidden(X33,X32)|X33=X31|X32!=k1_tarski(X31))&(X34!=X31|r2_hidden(X34,X32)|X32!=k1_tarski(X31)))&((~r2_hidden(esk4_2(X35,X36),X36)|esk4_2(X35,X36)!=X35|X36=k1_tarski(X35))&(r2_hidden(esk4_2(X35,X36),X36)|esk4_2(X35,X36)=X35|X36=k1_tarski(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.14/0.38  cnf(c_0_36, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_24]), c_0_24]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.14/0.38  cnf(c_0_37, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_39, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.38  cnf(c_0_40, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.38  cnf(c_0_41, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_32])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_17]), c_0_24]), c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.14/0.38  fof(c_0_43, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(r2_hidden(X14,X11)|r2_hidden(X14,X12))|X13!=k2_xboole_0(X11,X12))&((~r2_hidden(X15,X11)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))&(~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))))&(((~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17)))&(r2_hidden(esk2_3(X16,X17,X18),X18)|(r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k2_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.14/0.38  cnf(c_0_44, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_39]), c_0_17]), c_0_26]), c_0_27])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (esk5_0=k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.14/0.38  cnf(c_0_46, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.38  cnf(c_0_47, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.38  cnf(c_0_48, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_44])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (k3_enumset1(k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))),k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))),k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))),k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))),k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))))=k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45])).
% 0.14/0.38  cnf(c_0_50, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k3_enumset1(X2,X2,X2,X2,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_24]), c_0_26]), c_0_27])).
% 0.14/0.38  cnf(c_0_51, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k3_enumset1(X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_24]), c_0_26]), c_0_27])).
% 0.14/0.38  cnf(c_0_52, negated_conjecture, (X1=k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)))|~r2_hidden(X1,k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.14/0.38  cnf(c_0_53, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_50])).
% 0.14/0.38  fof(c_0_54, plain, ![X20]:(X20=k1_xboole_0|r2_hidden(esk3_1(X20),X20)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.14/0.38  cnf(c_0_55, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_51])).
% 0.14/0.38  cnf(c_0_56, negated_conjecture, (X1=k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.14/0.38  cnf(c_0_57, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, (X1=k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_52, c_0_55])).
% 0.14/0.38  cnf(c_0_60, negated_conjecture, (k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)))=esk3_1(esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.14/0.38  cnf(c_0_61, plain, (r2_hidden(esk4_2(X1,X2),X2)|esk4_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.38  cnf(c_0_62, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_63, negated_conjecture, (X1=esk3_1(esk6_0)|~r2_hidden(X1,esk7_0)), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.14/0.38  cnf(c_0_64, plain, (esk4_2(X1,X2)=X1|X2=k3_enumset1(X1,X1,X1,X1,X1)|r2_hidden(esk4_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_39]), c_0_17]), c_0_26]), c_0_27])).
% 0.14/0.38  cnf(c_0_65, negated_conjecture, (esk3_1(esk7_0)=k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_57]), c_0_62])).
% 0.14/0.38  cnf(c_0_66, plain, (X2=k1_tarski(X1)|~r2_hidden(esk4_2(X1,X2),X2)|esk4_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.38  cnf(c_0_67, negated_conjecture, (esk7_0=k3_enumset1(X1,X1,X1,X1,X1)|esk4_2(X1,esk7_0)=esk3_1(esk6_0)|esk4_2(X1,esk7_0)=X1), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.14/0.38  cnf(c_0_68, negated_conjecture, (r2_hidden(k3_tarski(k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_65]), c_0_62])).
% 0.14/0.38  cnf(c_0_69, plain, (X2=k3_enumset1(X1,X1,X1,X1,X1)|esk4_2(X1,X2)!=X1|~r2_hidden(esk4_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_39]), c_0_17]), c_0_26]), c_0_27])).
% 0.14/0.38  cnf(c_0_70, negated_conjecture, (esk7_0=k3_enumset1(esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0))|esk4_2(esk3_1(esk6_0),esk7_0)=esk3_1(esk6_0)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_67])])).
% 0.14/0.38  cnf(c_0_71, negated_conjecture, (r2_hidden(esk3_1(esk6_0),esk7_0)), inference(rw,[status(thm)],[c_0_68, c_0_60])).
% 0.14/0.38  cnf(c_0_72, negated_conjecture, (X1=esk3_1(esk6_0)|~r2_hidden(X1,esk6_0)), inference(rw,[status(thm)],[c_0_56, c_0_60])).
% 0.14/0.38  cnf(c_0_73, negated_conjecture, (esk6_0!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_74, negated_conjecture, (esk7_0=k3_enumset1(esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 0.14/0.38  cnf(c_0_75, negated_conjecture, (esk6_0=k3_enumset1(X1,X1,X1,X1,X1)|esk4_2(X1,esk6_0)=esk3_1(esk6_0)|esk4_2(X1,esk6_0)=X1), inference(spm,[status(thm)],[c_0_72, c_0_64])).
% 0.14/0.38  cnf(c_0_76, negated_conjecture, (k3_enumset1(esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0),esk3_1(esk6_0))!=esk6_0), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 0.14/0.38  cnf(c_0_77, negated_conjecture, (esk4_2(esk3_1(esk6_0),esk6_0)=esk3_1(esk6_0)), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_75])]), c_0_76])).
% 0.14/0.38  cnf(c_0_78, negated_conjecture, (~r2_hidden(esk3_1(esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_77]), c_0_76])).
% 0.14/0.38  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_57]), c_0_58]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 80
% 0.14/0.38  # Proof object clause steps            : 53
% 0.14/0.38  # Proof object formula steps           : 27
% 0.14/0.38  # Proof object conjectures             : 27
% 0.14/0.38  # Proof object clause conjectures      : 24
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 19
% 0.14/0.38  # Proof object initial formulas used   : 13
% 0.14/0.38  # Proof object generating inferences   : 16
% 0.14/0.38  # Proof object simplifying inferences  : 63
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 15
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 30
% 0.14/0.38  # Removed in clause preprocessing      : 6
% 0.14/0.38  # Initial clauses in saturation        : 24
% 0.14/0.38  # Processed clauses                    : 103
% 0.14/0.38  # ...of these trivial                  : 1
% 0.14/0.38  # ...subsumed                          : 11
% 0.14/0.38  # ...remaining for further processing  : 91
% 0.14/0.38  # Other redundant clauses eliminated   : 14
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 23
% 0.14/0.38  # Generated clauses                    : 194
% 0.14/0.38  # ...of the previous two non-trivial   : 169
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 171
% 0.14/0.38  # Factorizations                       : 10
% 0.14/0.38  # Equation resolutions                 : 14
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 38
% 0.14/0.38  #    Positive orientable unit clauses  : 10
% 0.14/0.38  #    Positive unorientable unit clauses: 3
% 0.14/0.38  #    Negative unit clauses             : 4
% 0.14/0.38  #    Non-unit-clauses                  : 21
% 0.14/0.38  # Current number of unprocessed clauses: 97
% 0.14/0.38  # ...number of literals in the above   : 296
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 52
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 125
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 115
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.14/0.38  # Unit Clause-clause subsumption calls : 43
% 0.14/0.38  # Rewrite failures with RHS unbound    : 17
% 0.14/0.38  # BW rewrite match attempts            : 48
% 0.14/0.38  # BW rewrite match successes           : 13
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 4426
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.035 s
% 0.14/0.38  # System time              : 0.002 s
% 0.14/0.38  # Total time               : 0.037 s
% 0.14/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
