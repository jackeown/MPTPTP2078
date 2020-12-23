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
% DateTime   : Thu Dec  3 10:38:06 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 (10403 expanded)
%              Number of clauses        :   44 (4463 expanded)
%              Number of leaves         :   13 (2946 expanded)
%              Depth                    :   15
%              Number of atoms          :  143 (14545 expanded)
%              Number of equality atoms :   94 (10442 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t20_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

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

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(c_0_13,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_15,plain,(
    ! [X16] : k4_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17])).

cnf(c_0_20,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

fof(c_0_21,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_22,plain,(
    ! [X19] : r1_xboole_0(X19,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_24,plain,(
    ! [X12] :
      ( X12 = k1_xboole_0
      | r2_hidden(esk2_1(X12),X12) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
      <=> X1 != X2 ) ),
    inference(assume_negation,[status(cth)],[t20_zfmisc_1])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) = k3_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_23])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_31,negated_conjecture,
    ( ( k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) != k1_tarski(esk5_0)
      | esk5_0 = esk6_0 )
    & ( k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) = k1_tarski(esk5_0)
      | esk5_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

fof(c_0_32,plain,(
    ! [X38] : k2_tarski(X38,X38) = k1_tarski(X38) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_33,plain,(
    ! [X39,X40] : k1_enumset1(X39,X39,X40) = k2_tarski(X39,X40) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_34,plain,(
    ! [X41,X42,X43] : k2_enumset1(X41,X41,X42,X43) = k1_enumset1(X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_35,plain,(
    ! [X44,X45,X46,X47] : k3_enumset1(X44,X44,X45,X46,X47) = k2_enumset1(X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_20]),c_0_30])).

fof(c_0_37,plain,(
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
      & ( esk3_4(X26,X27,X28,X29) != X26
        | ~ r2_hidden(esk3_4(X26,X27,X28,X29),X29)
        | X29 = k1_enumset1(X26,X27,X28) )
      & ( esk3_4(X26,X27,X28,X29) != X27
        | ~ r2_hidden(esk3_4(X26,X27,X28,X29),X29)
        | X29 = k1_enumset1(X26,X27,X28) )
      & ( esk3_4(X26,X27,X28,X29) != X28
        | ~ r2_hidden(esk3_4(X26,X27,X28,X29),X29)
        | X29 = k1_enumset1(X26,X27,X28) )
      & ( r2_hidden(esk3_4(X26,X27,X28,X29),X29)
        | esk3_4(X26,X27,X28,X29) = X26
        | esk3_4(X26,X27,X28,X29) = X27
        | esk3_4(X26,X27,X28,X29) = X28
        | X29 = k1_enumset1(X26,X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_38,negated_conjecture,
    ( esk5_0 = esk6_0
    | k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_28,c_0_36])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,X1) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_36])).

fof(c_0_45,plain,(
    ! [X48,X49] :
      ( r2_hidden(X48,X49)
      | r1_xboole_0(k1_tarski(X48),X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) = k1_tarski(esk5_0)
    | esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_48,negated_conjecture,
    ( esk6_0 = esk5_0
    | k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) != k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_17]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_29]),c_0_30])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_43]),c_0_36]),c_0_44])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_41]),c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) = k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | esk6_0 != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_17]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( esk6_0 = esk5_0
    | r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_29]),c_0_49])])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_29]),c_0_30])).

cnf(c_0_56,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).

cnf(c_0_59,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_23]),c_0_55])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_30])).

cnf(c_0_61,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_41]),c_0_42])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_64,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( esk6_0 = esk5_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_55])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk2_1(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_66]),c_0_66]),c_0_66]),c_0_66]),c_0_66]),c_0_36]),c_0_66]),c_0_66]),c_0_66]),c_0_66]),c_0_66]),c_0_36])).

cnf(c_0_69,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_66]),c_0_66]),c_0_66]),c_0_66]),c_0_66]),c_0_36]),c_0_67]),c_0_66])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69]),c_0_69]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.39  # and selection function SelectNegativeLiterals.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.028 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.39  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.39  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.39  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.39  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.39  fof(t20_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.19/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.39  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.39  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.19/0.39  fof(c_0_13, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.39  fof(c_0_14, plain, ![X14, X15]:k4_xboole_0(X14,X15)=k5_xboole_0(X14,k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.39  fof(c_0_15, plain, ![X16]:k4_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.39  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  cnf(c_0_18, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_19, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17])).
% 0.19/0.39  cnf(c_0_20, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 0.19/0.39  fof(c_0_21, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.39  fof(c_0_22, plain, ![X19]:r1_xboole_0(X19,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.39  cnf(c_0_23, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k3_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.39  fof(c_0_24, plain, ![X12]:(X12=k1_xboole_0|r2_hidden(esk2_1(X12),X12)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.39  cnf(c_0_25, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  cnf(c_0_26, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  fof(c_0_27, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2)), inference(assume_negation,[status(cth)],[t20_zfmisc_1])).
% 0.19/0.39  cnf(c_0_28, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))=k3_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_19, c_0_23])).
% 0.19/0.39  cnf(c_0_29, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.39  cnf(c_0_30, plain, (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.39  fof(c_0_31, negated_conjecture, ((k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))!=k1_tarski(esk5_0)|esk5_0=esk6_0)&(k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))=k1_tarski(esk5_0)|esk5_0!=esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.19/0.39  fof(c_0_32, plain, ![X38]:k2_tarski(X38,X38)=k1_tarski(X38), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.39  fof(c_0_33, plain, ![X39, X40]:k1_enumset1(X39,X39,X40)=k2_tarski(X39,X40), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.39  fof(c_0_34, plain, ![X41, X42, X43]:k2_enumset1(X41,X41,X42,X43)=k1_enumset1(X41,X42,X43), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.39  fof(c_0_35, plain, ![X44, X45, X46, X47]:k3_enumset1(X44,X44,X45,X46,X47)=k2_enumset1(X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.39  cnf(c_0_36, plain, (k3_xboole_0(X1,X1)=X1), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_20]), c_0_30])).
% 0.19/0.39  fof(c_0_37, plain, ![X20, X21, X22, X23, X24, X25, X26, X27, X28, X29]:(((~r2_hidden(X24,X23)|(X24=X20|X24=X21|X24=X22)|X23!=k1_enumset1(X20,X21,X22))&(((X25!=X20|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22))&(X25!=X21|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22)))&(X25!=X22|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22))))&((((esk3_4(X26,X27,X28,X29)!=X26|~r2_hidden(esk3_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28))&(esk3_4(X26,X27,X28,X29)!=X27|~r2_hidden(esk3_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28)))&(esk3_4(X26,X27,X28,X29)!=X28|~r2_hidden(esk3_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28)))&(r2_hidden(esk3_4(X26,X27,X28,X29),X29)|(esk3_4(X26,X27,X28,X29)=X26|esk3_4(X26,X27,X28,X29)=X27|esk3_4(X26,X27,X28,X29)=X28)|X29=k1_enumset1(X26,X27,X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (esk5_0=esk6_0|k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.39  cnf(c_0_39, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.39  cnf(c_0_40, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.39  cnf(c_0_41, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.39  cnf(c_0_42, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.39  cnf(c_0_43, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_28, c_0_36])).
% 0.19/0.39  cnf(c_0_44, plain, (k5_xboole_0(X1,X1)=k3_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_23, c_0_36])).
% 0.19/0.39  fof(c_0_45, plain, ![X48, X49]:(r2_hidden(X48,X49)|r1_xboole_0(k1_tarski(X48),X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.19/0.39  cnf(c_0_46, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))=k1_tarski(esk5_0)|esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.39  cnf(c_0_48, negated_conjecture, (esk6_0=esk5_0|k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))!=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_17]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42])).
% 0.19/0.39  cnf(c_0_49, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_29]), c_0_30])).
% 0.19/0.39  cnf(c_0_50, plain, (k3_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=k3_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_43]), c_0_36]), c_0_44])).
% 0.19/0.39  cnf(c_0_51, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.39  cnf(c_0_52, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_41]), c_0_42])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|esk6_0!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_17]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42])).
% 0.19/0.39  cnf(c_0_54, negated_conjecture, (esk6_0=esk5_0|r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_29]), c_0_49])])).
% 0.19/0.39  cnf(c_0_55, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_29]), c_0_30])).
% 0.19/0.39  cnf(c_0_56, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.39  cnf(c_0_57, plain, (r2_hidden(X1,X2)|r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.19/0.39  cnf(c_0_58, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).
% 0.19/0.39  cnf(c_0_59, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0|r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_23]), c_0_55])).
% 0.19/0.39  cnf(c_0_60, plain, (~r2_hidden(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_29]), c_0_30])).
% 0.19/0.39  cnf(c_0_61, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_41]), c_0_42])).
% 0.19/0.39  cnf(c_0_62, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2))), inference(spm,[status(thm)],[c_0_25, c_0_57])).
% 0.19/0.39  cnf(c_0_63, negated_conjecture, (r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.19/0.39  cnf(c_0_64, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_61])).
% 0.19/0.39  cnf(c_0_65, negated_conjecture, (r2_hidden(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.39  cnf(c_0_66, negated_conjecture, (esk6_0=esk5_0), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.39  cnf(c_0_67, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_44, c_0_55])).
% 0.19/0.39  cnf(c_0_68, negated_conjecture, (r2_hidden(esk2_1(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_66]), c_0_66]), c_0_66]), c_0_66]), c_0_66]), c_0_36]), c_0_66]), c_0_66]), c_0_66]), c_0_66]), c_0_66]), c_0_36])).
% 0.19/0.39  cnf(c_0_69, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_66]), c_0_66]), c_0_66]), c_0_66]), c_0_66]), c_0_36]), c_0_67]), c_0_66])])).
% 0.19/0.39  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69]), c_0_69]), c_0_60]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 71
% 0.19/0.39  # Proof object clause steps            : 44
% 0.19/0.39  # Proof object formula steps           : 27
% 0.19/0.39  # Proof object conjectures             : 15
% 0.19/0.39  # Proof object clause conjectures      : 12
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 15
% 0.19/0.39  # Proof object initial formulas used   : 13
% 0.19/0.39  # Proof object generating inferences   : 14
% 0.19/0.39  # Proof object simplifying inferences  : 83
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 14
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 26
% 0.19/0.39  # Removed in clause preprocessing      : 5
% 0.19/0.39  # Initial clauses in saturation        : 21
% 0.19/0.39  # Processed clauses                    : 139
% 0.19/0.39  # ...of these trivial                  : 5
% 0.19/0.39  # ...subsumed                          : 41
% 0.19/0.39  # ...remaining for further processing  : 93
% 0.19/0.39  # Other redundant clauses eliminated   : 36
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 1
% 0.19/0.39  # Backward-rewritten                   : 30
% 0.19/0.39  # Generated clauses                    : 600
% 0.19/0.39  # ...of the previous two non-trivial   : 506
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 562
% 0.19/0.39  # Factorizations                       : 6
% 0.19/0.39  # Equation resolutions                 : 36
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
% 0.19/0.39  # Current number of processed clauses  : 36
% 0.19/0.39  #    Positive orientable unit clauses  : 12
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 1
% 0.19/0.39  #    Non-unit-clauses                  : 23
% 0.19/0.39  # Current number of unprocessed clauses: 393
% 0.19/0.39  # ...number of literals in the above   : 1306
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 56
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 277
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 239
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 28
% 0.19/0.39  # Unit Clause-clause subsumption calls : 71
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 51
% 0.19/0.39  # BW rewrite match successes           : 12
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 10478
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.039 s
% 0.19/0.39  # System time              : 0.004 s
% 0.19/0.39  # Total time               : 0.043 s
% 0.19/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
