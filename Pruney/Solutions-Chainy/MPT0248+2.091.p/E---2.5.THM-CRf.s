%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:51 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 (2440 expanded)
%              Number of clauses        :   63 (1036 expanded)
%              Number of leaves         :   18 ( 689 expanded)
%              Depth                    :   14
%              Number of atoms          :  204 (3612 expanded)
%              Number of equality atoms :  121 (2828 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t43_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(c_0_18,plain,(
    ! [X55,X56] : k3_tarski(k2_tarski(X55,X56)) = k2_xboole_0(X55,X56) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X44,X45] : k1_enumset1(X44,X44,X45) = k2_tarski(X44,X45) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | k2_xboole_0(X27,X28) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_21,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X46,X47,X48] : k2_enumset1(X46,X46,X47,X48) = k1_enumset1(X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X49,X50,X51,X52] : k3_enumset1(X49,X49,X50,X51,X52) = k2_enumset1(X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X31] : k4_xboole_0(X31,k1_xboole_0) = X31 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_26,plain,(
    ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X22,k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_27,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(X24,X25)
      | r1_tarski(X24,k2_xboole_0(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_28,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_30,plain,(
    ! [X32,X33] : k4_xboole_0(X32,k2_xboole_0(X32,X33)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_35,plain,(
    ! [X30] : r1_tarski(k1_xboole_0,X30) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_36,plain,(
    ! [X34,X35] : k2_xboole_0(X34,X35) = k5_xboole_0(X34,k4_xboole_0(X35,X34)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_39,plain,(
    ! [X29] : k3_xboole_0(X29,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_42,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0)
    & ( esk5_0 != k1_tarski(esk4_0)
      | esk6_0 != k1_tarski(esk4_0) )
    & ( esk5_0 != k1_xboole_0
      | esk6_0 != k1_tarski(esk4_0) )
    & ( esk5_0 != k1_tarski(esk4_0)
      | esk6_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

fof(c_0_43,plain,(
    ! [X43] : k2_tarski(X43,X43) = k1_tarski(X43) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_50,plain,(
    ! [X53,X54] :
      ( ( ~ r1_tarski(X53,k1_tarski(X54))
        | X53 = k1_xboole_0
        | X53 = k1_tarski(X54) )
      & ( X53 != k1_xboole_0
        | r1_tarski(X53,k1_tarski(X54)) )
      & ( X53 != k1_tarski(X54)
        | r1_tarski(X53,k1_tarski(X54)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_56,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_32]),c_0_38]),c_0_33]),c_0_34])).

cnf(c_0_58,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_59,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_32]),c_0_38]),c_0_33]),c_0_34])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_22]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_64,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_46])).

cnf(c_0_65,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_67,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_49]),c_0_60]),c_0_58])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_54]),c_0_54]),c_0_22]),c_0_22]),c_0_33]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk6_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_70,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_71,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk1_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk6_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( esk5_0 != k1_tarski(esk4_0)
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_77,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k1_xboole_0)) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)
    | r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_71])).

cnf(c_0_78,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_72]),c_0_60]),c_0_60])).

cnf(c_0_79,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk6_0)) = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_80,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_75,c_0_38])).

cnf(c_0_81,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_82,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk5_0 != k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_54]),c_0_22]),c_0_33]),c_0_34])).

cnf(c_0_83,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk5_0
    | r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk5_0)) = esk6_0
    | esk6_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_79]),c_0_60])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_46])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_71])).

cnf(c_0_88,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_84])).

cnf(c_0_89,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_49]),c_0_60]),c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])).

cnf(c_0_91,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | esk6_0 != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_92,negated_conjecture,
    ( esk5_0 != k1_tarski(esk4_0)
    | esk6_0 != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_93,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_90]),c_0_63])).

cnf(c_0_94,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | esk6_0 != k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_54]),c_0_22]),c_0_33]),c_0_34])).

cnf(c_0_95,negated_conjecture,
    ( esk5_0 != k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)
    | esk6_0 != k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_54]),c_0_54]),c_0_22]),c_0_22]),c_0_33]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_96,negated_conjecture,
    ( X1 = k1_xboole_0
    | X1 = esk6_0
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_93])])).

cnf(c_0_98,negated_conjecture,
    ( esk6_0 != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_93]),c_0_93])])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_90]),c_0_97]),c_0_98]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.20/0.39  # and selection function SelectNegativeLiterals.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.013 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.39  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.39  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.39  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.20/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.39  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.20/0.39  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.20/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.39  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.39  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.39  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.20/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.39  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.39  fof(c_0_18, plain, ![X55, X56]:k3_tarski(k2_tarski(X55,X56))=k2_xboole_0(X55,X56), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.39  fof(c_0_19, plain, ![X44, X45]:k1_enumset1(X44,X44,X45)=k2_tarski(X44,X45), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.39  fof(c_0_20, plain, ![X27, X28]:(~r1_tarski(X27,X28)|k2_xboole_0(X27,X28)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.39  cnf(c_0_21, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  fof(c_0_23, plain, ![X46, X47, X48]:k2_enumset1(X46,X46,X47,X48)=k1_enumset1(X46,X47,X48), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.39  fof(c_0_24, plain, ![X49, X50, X51, X52]:k3_enumset1(X49,X49,X50,X51,X52)=k2_enumset1(X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.39  fof(c_0_25, plain, ![X31]:k4_xboole_0(X31,k1_xboole_0)=X31, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.39  fof(c_0_26, plain, ![X22, X23]:k4_xboole_0(X22,X23)=k5_xboole_0(X22,k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.39  fof(c_0_27, plain, ![X24, X25, X26]:(~r1_tarski(X24,X25)|r1_tarski(X24,k2_xboole_0(X26,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.20/0.39  fof(c_0_28, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.39  fof(c_0_29, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.20/0.39  fof(c_0_30, plain, ![X32, X33]:k4_xboole_0(X32,k2_xboole_0(X32,X33))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.20/0.39  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_32, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.39  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  fof(c_0_35, plain, ![X30]:r1_tarski(k1_xboole_0,X30), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.39  fof(c_0_36, plain, ![X34, X35]:k2_xboole_0(X34,X35)=k5_xboole_0(X34,k4_xboole_0(X35,X34)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.39  cnf(c_0_37, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  fof(c_0_39, plain, ![X29]:k3_xboole_0(X29,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.39  cnf(c_0_40, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_41, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  fof(c_0_42, negated_conjecture, (((k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)&(esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_tarski(esk4_0)))&(esk5_0!=k1_xboole_0|esk6_0!=k1_tarski(esk4_0)))&(esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.20/0.39  fof(c_0_43, plain, ![X43]:k2_tarski(X43,X43)=k1_tarski(X43), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.39  cnf(c_0_44, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_45, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])).
% 0.20/0.39  cnf(c_0_46, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.39  cnf(c_0_47, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.39  cnf(c_0_48, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.39  cnf(c_0_49, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.39  fof(c_0_50, plain, ![X53, X54]:((~r1_tarski(X53,k1_tarski(X54))|(X53=k1_xboole_0|X53=k1_tarski(X54)))&((X53!=k1_xboole_0|r1_tarski(X53,k1_tarski(X54)))&(X53!=k1_tarski(X54)|r1_tarski(X53,k1_tarski(X54))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.20/0.39  cnf(c_0_51, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_32]), c_0_33]), c_0_34])).
% 0.20/0.39  cnf(c_0_52, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_41])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.39  cnf(c_0_54, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.39  cnf(c_0_55, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  fof(c_0_56, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.39  cnf(c_0_57, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_32]), c_0_38]), c_0_33]), c_0_34])).
% 0.20/0.39  cnf(c_0_58, plain, (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.39  cnf(c_0_59, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_32]), c_0_38]), c_0_33]), c_0_34])).
% 0.20/0.39  cnf(c_0_60, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.39  cnf(c_0_61, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.39  cnf(c_0_62, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_22]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34])).
% 0.20/0.39  cnf(c_0_64, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_46])).
% 0.20/0.39  cnf(c_0_65, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.39  cnf(c_0_66, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.39  cnf(c_0_67, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_49]), c_0_60]), c_0_58])).
% 0.20/0.39  cnf(c_0_68, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|~r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_54]), c_0_54]), c_0_22]), c_0_22]), c_0_33]), c_0_33]), c_0_34]), c_0_34])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (r1_tarski(esk6_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.39  fof(c_0_70, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.39  cnf(c_0_71, plain, (k1_xboole_0=X1|r2_hidden(esk1_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.39  cnf(c_0_72, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_63])).
% 0.20/0.39  cnf(c_0_74, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk6_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.39  cnf(c_0_75, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.39  cnf(c_0_76, negated_conjecture, (esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.39  cnf(c_0_77, negated_conjecture, (k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k1_xboole_0))=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)|r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)), inference(spm,[status(thm)],[c_0_63, c_0_71])).
% 0.20/0.39  cnf(c_0_78, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_72]), c_0_60]), c_0_60])).
% 0.20/0.39  cnf(c_0_79, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk6_0))=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.39  cnf(c_0_80, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_75, c_0_38])).
% 0.20/0.39  cnf(c_0_81, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.39  cnf(c_0_82, negated_conjecture, (esk6_0!=k1_xboole_0|esk5_0!=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_54]), c_0_22]), c_0_33]), c_0_34])).
% 0.20/0.39  cnf(c_0_83, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk5_0|r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)), inference(rw,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.39  cnf(c_0_84, negated_conjecture, (k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk5_0))=esk6_0|esk6_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_79]), c_0_60])).
% 0.20/0.39  cnf(c_0_85, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_80])).
% 0.20/0.39  cnf(c_0_86, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_81, c_0_46])).
% 0.20/0.39  cnf(c_0_87, negated_conjecture, (r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_71])).
% 0.20/0.39  cnf(c_0_88, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_62, c_0_84])).
% 0.20/0.39  cnf(c_0_89, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_49]), c_0_60]), c_0_86])).
% 0.20/0.39  cnf(c_0_90, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])).
% 0.20/0.39  cnf(c_0_91, negated_conjecture, (esk5_0!=k1_xboole_0|esk6_0!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.39  cnf(c_0_92, negated_conjecture, (esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.39  cnf(c_0_93, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_90]), c_0_63])).
% 0.20/0.39  cnf(c_0_94, negated_conjecture, (esk5_0!=k1_xboole_0|esk6_0!=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_54]), c_0_22]), c_0_33]), c_0_34])).
% 0.20/0.39  cnf(c_0_95, negated_conjecture, (esk5_0!=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)|esk6_0!=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_54]), c_0_54]), c_0_22]), c_0_22]), c_0_33]), c_0_33]), c_0_34]), c_0_34])).
% 0.20/0.39  cnf(c_0_96, negated_conjecture, (X1=k1_xboole_0|X1=esk6_0|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_68, c_0_93])).
% 0.20/0.39  cnf(c_0_97, negated_conjecture, (esk5_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_93])])).
% 0.20/0.39  cnf(c_0_98, negated_conjecture, (esk6_0!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_93]), c_0_93])])).
% 0.20/0.39  cnf(c_0_99, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_90]), c_0_97]), c_0_98]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 100
% 0.20/0.39  # Proof object clause steps            : 63
% 0.20/0.39  # Proof object formula steps           : 37
% 0.20/0.39  # Proof object conjectures             : 26
% 0.20/0.39  # Proof object clause conjectures      : 23
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 23
% 0.20/0.39  # Proof object initial formulas used   : 18
% 0.20/0.39  # Proof object generating inferences   : 21
% 0.20/0.39  # Proof object simplifying inferences  : 70
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 19
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 36
% 0.20/0.39  # Removed in clause preprocessing      : 6
% 0.20/0.39  # Initial clauses in saturation        : 30
% 0.20/0.39  # Processed clauses                    : 692
% 0.20/0.39  # ...of these trivial                  : 31
% 0.20/0.39  # ...subsumed                          : 419
% 0.20/0.39  # ...remaining for further processing  : 242
% 0.20/0.39  # Other redundant clauses eliminated   : 306
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 20
% 0.20/0.39  # Backward-rewritten                   : 41
% 0.20/0.39  # Generated clauses                    : 6096
% 0.20/0.39  # ...of the previous two non-trivial   : 4424
% 0.20/0.39  # Contextual simplify-reflections      : 9
% 0.20/0.39  # Paramodulations                      : 5789
% 0.20/0.39  # Factorizations                       : 2
% 0.20/0.39  # Equation resolutions                 : 306
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 145
% 0.20/0.39  #    Positive orientable unit clauses  : 29
% 0.20/0.39  #    Positive unorientable unit clauses: 1
% 0.20/0.39  #    Negative unit clauses             : 3
% 0.20/0.39  #    Non-unit-clauses                  : 112
% 0.20/0.39  # Current number of unprocessed clauses: 3702
% 0.20/0.39  # ...number of literals in the above   : 11060
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 94
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 2756
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 2477
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 370
% 0.20/0.39  # Unit Clause-clause subsumption calls : 288
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 67
% 0.20/0.39  # BW rewrite match successes           : 26
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 82339
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.046 s
% 0.20/0.39  # System time              : 0.005 s
% 0.20/0.39  # Total time               : 0.051 s
% 0.20/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
