%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:06 EST 2020

% Result     : Theorem 9.47s
% Output     : CNFRefutation 9.47s
% Verified   : 
% Statistics : Number of formulae       :   95 (1185 expanded)
%              Number of clauses        :   54 ( 478 expanded)
%              Number of leaves         :   20 ( 347 expanded)
%              Depth                    :   12
%              Number of atoms          :  207 (1829 expanded)
%              Number of equality atoms :   57 (1032 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t13_ordinal1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t144_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(X1,X2)
        & r2_hidden(X3,k2_xboole_0(X1,X2))
        & ~ ( r2_hidden(X3,X1)
            & ~ r2_hidden(X3,X2) )
        & ~ ( r2_hidden(X3,X2)
            & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t8_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(k1_setfam_1(X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(c_0_20,plain,(
    ! [X49,X50,X51] :
      ( ( r2_hidden(X49,X51)
        | ~ r1_tarski(k2_tarski(X49,X50),X51) )
      & ( r2_hidden(X50,X51)
        | ~ r1_tarski(k2_tarski(X49,X50),X51) )
      & ( ~ r2_hidden(X49,X51)
        | ~ r2_hidden(X50,X51)
        | r1_tarski(k2_tarski(X49,X50),X51) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_21,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X27,X28,X29,X30] : k3_enumset1(X27,X27,X28,X29,X30) = k2_enumset1(X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X31,X32,X33,X34,X35] : k4_enumset1(X31,X31,X32,X33,X34,X35) = k3_enumset1(X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_25,plain,(
    ! [X36,X37,X38,X39,X40,X41] : k5_enumset1(X36,X36,X37,X38,X39,X40,X41) = k4_enumset1(X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_26,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,k1_ordinal1(X2))
      <=> ( r2_hidden(X1,X2)
          | X1 = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t13_ordinal1])).

fof(c_0_28,plain,(
    ! [X56] : k1_ordinal1(X56) = k2_xboole_0(X56,k1_tarski(X56)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_29,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_30,plain,(
    ! [X44,X45] : k3_tarski(k2_tarski(X44,X45)) = k2_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_39,negated_conjecture,
    ( ( ~ r2_hidden(esk2_0,esk3_0)
      | ~ r2_hidden(esk2_0,k1_ordinal1(esk3_0)) )
    & ( esk2_0 != esk3_0
      | ~ r2_hidden(esk2_0,k1_ordinal1(esk3_0)) )
    & ( r2_hidden(esk2_0,k1_ordinal1(esk3_0))
      | r2_hidden(esk2_0,esk3_0)
      | esk2_0 = esk3_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])])).

cnf(c_0_40,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_43,plain,(
    ! [X42,X43] :
      ( ~ r2_hidden(X42,X43)
      | r1_tarski(X42,k3_tarski(X43)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

fof(c_0_47,plain,(
    ! [X46,X47,X48] :
      ( r2_hidden(X46,X48)
      | r2_hidden(X47,X48)
      | X48 = k4_xboole_0(X48,k2_tarski(X46,X47)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).

cnf(c_0_48,negated_conjecture,
    ( esk2_0 != esk3_0
    | ~ r2_hidden(esk2_0,k1_ordinal1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_42,c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk2_0,k1_ordinal1(esk3_0))
    | r2_hidden(esk2_0,esk3_0)
    | esk2_0 = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_54,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_45])).

fof(c_0_56,plain,(
    ! [X14,X15,X16] :
      ( ( r2_hidden(X16,X15)
        | r2_hidden(X16,X14)
        | ~ r1_xboole_0(X14,X15)
        | ~ r2_hidden(X16,k2_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X16,X14)
        | r2_hidden(X16,X14)
        | ~ r1_xboole_0(X14,X15)
        | ~ r2_hidden(X16,k2_xboole_0(X14,X15)) )
      & ( r2_hidden(X16,X15)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15)
        | ~ r2_hidden(X16,k2_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15)
        | ~ r2_hidden(X16,k2_xboole_0(X14,X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_xboole_0])])])])).

fof(c_0_57,plain,(
    ! [X19,X20] :
      ( ( ~ r1_xboole_0(X19,X20)
        | k4_xboole_0(X19,X20) = X19 )
      & ( k4_xboole_0(X19,X20) != X19
        | r1_xboole_0(X19,X20) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | X2 = k4_xboole_0(X2,k2_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( esk3_0 != esk2_0
    | ~ r2_hidden(esk2_0,k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_32]),c_0_50]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36])).

cnf(c_0_60,negated_conjecture,
    ( esk3_0 = esk2_0
    | r2_hidden(esk2_0,esk3_0)
    | r2_hidden(esk2_0,k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_49]),c_0_32]),c_0_50]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_62,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_55])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r1_xboole_0(X3,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,plain,
    ( X2 = k4_xboole_0(X2,k5_enumset1(X1,X1,X1,X1,X1,X1,X3))
    | r2_hidden(X3,X2)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

fof(c_0_67,plain,(
    ! [X57,X58] :
      ( ~ r2_hidden(X57,X58)
      | ~ r1_tarski(X58,X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0)
    | ~ r2_hidden(esk2_0,k1_ordinal1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk2_0,k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))
    | r2_hidden(esk2_0,esk3_0)
    | ~ r2_hidden(esk3_0,k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X1)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_61])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X2)
    | ~ r1_xboole_0(X3,X2)
    | ~ r2_hidden(X1,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_50]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X3))
    | r2_hidden(X2,X1)
    | r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0)
    | ~ r2_hidden(esk2_0,k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_49]),c_0_32]),c_0_50]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk2_0,k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])]),c_0_71])).

fof(c_0_77,plain,(
    ! [X13] : k2_xboole_0(X13,X13) = X13 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X3))
    | r2_hidden(X3,X4)
    | r2_hidden(X2,X4)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_45])).

cnf(c_0_80,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])])).

cnf(c_0_81,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

fof(c_0_82,plain,(
    ! [X53,X54,X55] :
      ( ~ r2_hidden(X53,X54)
      | ~ r1_tarski(X53,X55)
      | r1_tarski(k1_setfam_1(X54),X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).

fof(c_0_83,plain,(
    ! [X52] : k1_setfam_1(k1_tarski(X52)) = X52 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk2_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_76]),c_0_79]),c_0_80])).

cnf(c_0_85,plain,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_50]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_86,plain,
    ( r1_tarski(k1_setfam_1(X2),X3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_87,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_88,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_84]),c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_76])])).

cnf(c_0_91,plain,
    ( r1_tarski(k1_setfam_1(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_45])).

cnf(c_0_92,plain,
    ( k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_41]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_93,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_84]),c_0_92]),c_0_93]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 9.47/9.65  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 9.47/9.65  # and selection function SelectNegativeLiterals.
% 9.47/9.65  #
% 9.47/9.65  # Preprocessing time       : 0.028 s
% 9.47/9.65  # Presaturation interreduction done
% 9.47/9.65  
% 9.47/9.65  # Proof found!
% 9.47/9.65  # SZS status Theorem
% 9.47/9.65  # SZS output start CNFRefutation
% 9.47/9.65  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 9.47/9.65  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 9.47/9.65  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 9.47/9.65  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 9.47/9.65  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 9.47/9.65  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 9.47/9.65  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.47/9.65  fof(t13_ordinal1, conjecture, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 9.47/9.65  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 9.47/9.65  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 9.47/9.65  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.47/9.65  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 9.47/9.65  fof(t144_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 9.47/9.65  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.47/9.65  fof(t5_xboole_0, axiom, ![X1, X2, X3]:~((((r1_xboole_0(X1,X2)&r2_hidden(X3,k2_xboole_0(X1,X2)))&~((r2_hidden(X3,X1)&~(r2_hidden(X3,X2)))))&~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_xboole_0)).
% 9.47/9.65  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 9.47/9.65  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 9.47/9.65  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 9.47/9.65  fof(t8_setfam_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(k1_setfam_1(X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_setfam_1)).
% 9.47/9.65  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 9.47/9.65  fof(c_0_20, plain, ![X49, X50, X51]:(((r2_hidden(X49,X51)|~r1_tarski(k2_tarski(X49,X50),X51))&(r2_hidden(X50,X51)|~r1_tarski(k2_tarski(X49,X50),X51)))&(~r2_hidden(X49,X51)|~r2_hidden(X50,X51)|r1_tarski(k2_tarski(X49,X50),X51))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 9.47/9.65  fof(c_0_21, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 9.47/9.65  fof(c_0_22, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 9.47/9.65  fof(c_0_23, plain, ![X27, X28, X29, X30]:k3_enumset1(X27,X27,X28,X29,X30)=k2_enumset1(X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 9.47/9.65  fof(c_0_24, plain, ![X31, X32, X33, X34, X35]:k4_enumset1(X31,X31,X32,X33,X34,X35)=k3_enumset1(X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 9.47/9.65  fof(c_0_25, plain, ![X36, X37, X38, X39, X40, X41]:k5_enumset1(X36,X36,X37,X38,X39,X40,X41)=k4_enumset1(X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 9.47/9.65  fof(c_0_26, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 9.47/9.65  fof(c_0_27, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2))), inference(assume_negation,[status(cth)],[t13_ordinal1])).
% 9.47/9.65  fof(c_0_28, plain, ![X56]:k1_ordinal1(X56)=k2_xboole_0(X56,k1_tarski(X56)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 9.47/9.65  fof(c_0_29, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 9.47/9.65  fof(c_0_30, plain, ![X44, X45]:k3_tarski(k2_tarski(X44,X45))=k2_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 9.47/9.65  cnf(c_0_31, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 9.47/9.65  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 9.47/9.65  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 9.47/9.65  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 9.47/9.65  cnf(c_0_35, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 9.47/9.65  cnf(c_0_36, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 9.47/9.65  cnf(c_0_37, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 9.47/9.65  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 9.47/9.65  fof(c_0_39, negated_conjecture, (((~r2_hidden(esk2_0,esk3_0)|~r2_hidden(esk2_0,k1_ordinal1(esk3_0)))&(esk2_0!=esk3_0|~r2_hidden(esk2_0,k1_ordinal1(esk3_0))))&(r2_hidden(esk2_0,k1_ordinal1(esk3_0))|(r2_hidden(esk2_0,esk3_0)|esk2_0=esk3_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])])).
% 9.47/9.65  cnf(c_0_40, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 9.47/9.65  cnf(c_0_41, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 9.47/9.65  cnf(c_0_42, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.47/9.65  fof(c_0_43, plain, ![X42, X43]:(~r2_hidden(X42,X43)|r1_tarski(X42,k3_tarski(X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 9.47/9.65  cnf(c_0_44, plain, (r2_hidden(X1,X2)|~r1_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 9.47/9.65  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_37])).
% 9.47/9.65  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 9.47/9.65  fof(c_0_47, plain, ![X46, X47, X48]:(r2_hidden(X46,X48)|r2_hidden(X47,X48)|X48=k4_xboole_0(X48,k2_tarski(X46,X47))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).
% 9.47/9.65  cnf(c_0_48, negated_conjecture, (esk2_0!=esk3_0|~r2_hidden(esk2_0,k1_ordinal1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 9.47/9.65  cnf(c_0_49, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 9.47/9.65  cnf(c_0_50, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_42, c_0_32])).
% 9.47/9.65  cnf(c_0_51, negated_conjecture, (r2_hidden(esk2_0,k1_ordinal1(esk3_0))|r2_hidden(esk2_0,esk3_0)|esk2_0=esk3_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 9.47/9.65  cnf(c_0_52, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 9.47/9.65  cnf(c_0_53, plain, (r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 9.47/9.65  fof(c_0_54, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 9.47/9.65  cnf(c_0_55, plain, (r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_46, c_0_45])).
% 9.47/9.65  fof(c_0_56, plain, ![X14, X15, X16]:(((r2_hidden(X16,X15)|(r2_hidden(X16,X14)|(~r1_xboole_0(X14,X15)|~r2_hidden(X16,k2_xboole_0(X14,X15)))))&(~r2_hidden(X16,X14)|(r2_hidden(X16,X14)|(~r1_xboole_0(X14,X15)|~r2_hidden(X16,k2_xboole_0(X14,X15))))))&((r2_hidden(X16,X15)|(~r2_hidden(X16,X15)|(~r1_xboole_0(X14,X15)|~r2_hidden(X16,k2_xboole_0(X14,X15)))))&(~r2_hidden(X16,X14)|(~r2_hidden(X16,X15)|(~r1_xboole_0(X14,X15)|~r2_hidden(X16,k2_xboole_0(X14,X15))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_xboole_0])])])])).
% 9.47/9.65  fof(c_0_57, plain, ![X19, X20]:((~r1_xboole_0(X19,X20)|k4_xboole_0(X19,X20)=X19)&(k4_xboole_0(X19,X20)!=X19|r1_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 9.47/9.65  cnf(c_0_58, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|X2=k4_xboole_0(X2,k2_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 9.47/9.65  cnf(c_0_59, negated_conjecture, (esk3_0!=esk2_0|~r2_hidden(esk2_0,k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_32]), c_0_50]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36])).
% 9.47/9.65  cnf(c_0_60, negated_conjecture, (esk3_0=esk2_0|r2_hidden(esk2_0,esk3_0)|r2_hidden(esk2_0,k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_49]), c_0_32]), c_0_50]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36])).
% 9.47/9.65  cnf(c_0_61, plain, (r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 9.47/9.65  cnf(c_0_62, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 9.47/9.65  cnf(c_0_63, plain, (r1_tarski(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_52, c_0_55])).
% 9.47/9.65  cnf(c_0_64, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r1_xboole_0(X3,X2)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 9.47/9.65  cnf(c_0_65, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 9.47/9.65  cnf(c_0_66, plain, (X2=k4_xboole_0(X2,k5_enumset1(X1,X1,X1,X1,X1,X1,X3))|r2_hidden(X3,X2)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 9.47/9.65  fof(c_0_67, plain, ![X57, X58]:(~r2_hidden(X57,X58)|~r1_tarski(X58,X57)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 9.47/9.65  cnf(c_0_68, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)|~r2_hidden(esk2_0,k1_ordinal1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 9.47/9.65  cnf(c_0_69, negated_conjecture, (r2_hidden(esk2_0,k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))|r2_hidden(esk2_0,esk3_0)|~r2_hidden(esk3_0,k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 9.47/9.65  cnf(c_0_70, plain, (r2_hidden(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X1))))), inference(spm,[status(thm)],[c_0_44, c_0_61])).
% 9.47/9.65  cnf(c_0_71, plain, (r2_hidden(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 9.47/9.65  cnf(c_0_72, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X2)|~r1_xboole_0(X3,X2)|~r2_hidden(X1,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_50]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 9.47/9.65  cnf(c_0_73, plain, (r1_xboole_0(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X3))|r2_hidden(X2,X1)|r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 9.47/9.65  cnf(c_0_74, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 9.47/9.65  cnf(c_0_75, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)|~r2_hidden(esk2_0,k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_49]), c_0_32]), c_0_50]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36])).
% 9.47/9.65  cnf(c_0_76, negated_conjecture, (r2_hidden(esk2_0,k3_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70])]), c_0_71])).
% 9.47/9.65  fof(c_0_77, plain, ![X13]:k2_xboole_0(X13,X13)=X13, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 9.47/9.65  cnf(c_0_78, plain, (r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X3))|r2_hidden(X3,X4)|r2_hidden(X2,X4)|r2_hidden(X1,X4)|~r2_hidden(X1,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,k5_enumset1(X2,X2,X2,X2,X2,X2,X3))))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 9.47/9.65  cnf(c_0_79, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_74, c_0_45])).
% 9.47/9.65  cnf(c_0_80, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])])).
% 9.47/9.65  cnf(c_0_81, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_77])).
% 9.47/9.65  fof(c_0_82, plain, ![X53, X54, X55]:(~r2_hidden(X53,X54)|~r1_tarski(X53,X55)|r1_tarski(k1_setfam_1(X54),X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).
% 9.47/9.65  fof(c_0_83, plain, ![X52]:k1_setfam_1(k1_tarski(X52))=X52, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 9.47/9.65  cnf(c_0_84, negated_conjecture, (r2_hidden(esk2_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_76]), c_0_79]), c_0_80])).
% 9.47/9.65  cnf(c_0_85, plain, (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_50]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 9.47/9.65  cnf(c_0_86, plain, (r1_tarski(k1_setfam_1(X2),X3)|~r2_hidden(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 9.47/9.65  cnf(c_0_87, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_83])).
% 9.47/9.65  cnf(c_0_88, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 9.47/9.65  cnf(c_0_89, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_84]), c_0_85])).
% 9.47/9.65  cnf(c_0_90, negated_conjecture, (esk2_0!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_76])])).
% 9.47/9.65  cnf(c_0_91, plain, (r1_tarski(k1_setfam_1(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_86, c_0_45])).
% 9.47/9.65  cnf(c_0_92, plain, (k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_41]), c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 9.47/9.65  cnf(c_0_93, negated_conjecture, (~r1_tarski(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])).
% 9.47/9.65  cnf(c_0_94, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_84]), c_0_92]), c_0_93]), ['proof']).
% 9.47/9.65  # SZS output end CNFRefutation
% 9.47/9.65  # Proof object total steps             : 95
% 9.47/9.65  # Proof object clause steps            : 54
% 9.47/9.65  # Proof object formula steps           : 41
% 9.47/9.65  # Proof object conjectures             : 17
% 9.47/9.65  # Proof object clause conjectures      : 14
% 9.47/9.65  # Proof object formula conjectures     : 3
% 9.47/9.65  # Proof object initial clauses used    : 24
% 9.47/9.65  # Proof object initial formulas used   : 20
% 9.47/9.65  # Proof object generating inferences   : 15
% 9.47/9.65  # Proof object simplifying inferences  : 80
% 9.47/9.65  # Training examples: 0 positive, 0 negative
% 9.47/9.65  # Parsed axioms                        : 20
% 9.47/9.65  # Removed by relevancy pruning/SinE    : 0
% 9.47/9.65  # Initial clauses                      : 32
% 9.47/9.65  # Removed in clause preprocessing      : 10
% 9.47/9.65  # Initial clauses in saturation        : 22
% 9.47/9.65  # Processed clauses                    : 8009
% 9.47/9.65  # ...of these trivial                  : 112
% 9.47/9.65  # ...subsumed                          : 4840
% 9.47/9.65  # ...remaining for further processing  : 3056
% 9.47/9.65  # Other redundant clauses eliminated   : 48
% 9.47/9.65  # Clauses deleted for lack of memory   : 0
% 9.47/9.65  # Backward-subsumed                    : 68
% 9.47/9.65  # Backward-rewritten                   : 39
% 9.47/9.65  # Generated clauses                    : 585340
% 9.47/9.65  # ...of the previous two non-trivial   : 552457
% 9.47/9.65  # Contextual simplify-reflections      : 119
% 9.47/9.65  # Paramodulations                      : 585216
% 9.47/9.65  # Factorizations                       : 76
% 9.47/9.65  # Equation resolutions                 : 48
% 9.47/9.65  # Propositional unsat checks           : 0
% 9.47/9.65  #    Propositional check models        : 0
% 9.47/9.65  #    Propositional check unsatisfiable : 0
% 9.47/9.65  #    Propositional clauses             : 0
% 9.47/9.65  #    Propositional clauses after purity: 0
% 9.47/9.65  #    Propositional unsat core size     : 0
% 9.47/9.65  #    Propositional preprocessing time  : 0.000
% 9.47/9.65  #    Propositional encoding time       : 0.000
% 9.47/9.65  #    Propositional solver time         : 0.000
% 9.47/9.65  #    Success case prop preproc time    : 0.000
% 9.47/9.65  #    Success case prop encoding time   : 0.000
% 9.47/9.65  #    Success case prop solver time     : 0.000
% 9.47/9.65  # Current number of processed clauses  : 2926
% 9.47/9.65  #    Positive orientable unit clauses  : 82
% 9.47/9.65  #    Positive unorientable unit clauses: 0
% 9.47/9.65  #    Negative unit clauses             : 48
% 9.47/9.65  #    Non-unit-clauses                  : 2796
% 9.47/9.65  # Current number of unprocessed clauses: 544134
% 9.47/9.65  # ...number of literals in the above   : 3119082
% 9.47/9.65  # Current number of archived formulas  : 0
% 9.47/9.65  # Current number of archived clauses   : 136
% 9.47/9.65  # Clause-clause subsumption calls (NU) : 460574
% 9.47/9.65  # Rec. Clause-clause subsumption calls : 198249
% 9.47/9.65  # Non-unit clause-clause subsumptions  : 4511
% 9.47/9.65  # Unit Clause-clause subsumption calls : 5524
% 9.47/9.65  # Rewrite failures with RHS unbound    : 0
% 9.47/9.65  # BW rewrite match attempts            : 616
% 9.47/9.65  # BW rewrite match successes           : 14
% 9.47/9.65  # Condensation attempts                : 0
% 9.47/9.65  # Condensation successes               : 0
% 9.47/9.65  # Termbank termtop insertions          : 29609436
% 9.47/9.67  
% 9.47/9.67  # -------------------------------------------------
% 9.47/9.67  # User time                : 9.059 s
% 9.47/9.67  # System time              : 0.274 s
% 9.47/9.67  # Total time               : 9.333 s
% 9.47/9.67  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
