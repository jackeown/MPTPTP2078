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
% DateTime   : Thu Dec  3 10:44:40 EST 2020

% Result     : Theorem 0.44s
% Output     : CNFRefutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  142 (18797 expanded)
%              Number of clauses        :  105 (8056 expanded)
%              Number of leaves         :   18 (5080 expanded)
%              Depth                    :   24
%              Number of atoms          :  292 (39946 expanded)
%              Number of equality atoms :  157 (22017 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   25 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t148_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & k3_xboole_0(X2,X3) = k1_tarski(X4)
        & r2_hidden(X4,X1) )
     => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(t142_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(X4,k1_enumset1(X1,X2,X3))
    <=> ~ ( X4 != k1_xboole_0
          & X4 != k1_tarski(X1)
          & X4 != k1_tarski(X2)
          & X4 != k1_tarski(X3)
          & X4 != k2_tarski(X1,X2)
          & X4 != k2_tarski(X2,X3)
          & X4 != k2_tarski(X1,X3)
          & X4 != k1_enumset1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & k3_xboole_0(X2,X3) = k1_tarski(X4)
          & r2_hidden(X4,X1) )
       => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    inference(assume_negation,[status(cth)],[t148_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X50,X51,X52,X53] :
      ( ( ~ r1_tarski(X53,k1_enumset1(X50,X51,X52))
        | X53 = k1_xboole_0
        | X53 = k1_tarski(X50)
        | X53 = k1_tarski(X51)
        | X53 = k1_tarski(X52)
        | X53 = k2_tarski(X50,X51)
        | X53 = k2_tarski(X51,X52)
        | X53 = k2_tarski(X50,X52)
        | X53 = k1_enumset1(X50,X51,X52) )
      & ( X53 != k1_xboole_0
        | r1_tarski(X53,k1_enumset1(X50,X51,X52)) )
      & ( X53 != k1_tarski(X50)
        | r1_tarski(X53,k1_enumset1(X50,X51,X52)) )
      & ( X53 != k1_tarski(X51)
        | r1_tarski(X53,k1_enumset1(X50,X51,X52)) )
      & ( X53 != k1_tarski(X52)
        | r1_tarski(X53,k1_enumset1(X50,X51,X52)) )
      & ( X53 != k2_tarski(X50,X51)
        | r1_tarski(X53,k1_enumset1(X50,X51,X52)) )
      & ( X53 != k2_tarski(X51,X52)
        | r1_tarski(X53,k1_enumset1(X50,X51,X52)) )
      & ( X53 != k2_tarski(X50,X52)
        | r1_tarski(X53,k1_enumset1(X50,X51,X52)) )
      & ( X53 != k1_enumset1(X50,X51,X52)
        | r1_tarski(X53,k1_enumset1(X50,X51,X52)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).

fof(c_0_20,plain,(
    ! [X43,X44,X45] : k2_enumset1(X43,X43,X44,X45) = k1_enumset1(X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_21,plain,(
    ! [X46,X47,X48,X49] : k3_enumset1(X46,X46,X47,X48,X49) = k2_enumset1(X46,X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_22,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_23,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & k3_xboole_0(esk4_0,esk5_0) = k1_tarski(esk6_0)
    & r2_hidden(esk6_0,esk3_0)
    & k3_xboole_0(esk3_0,esk5_0) != k1_tarski(esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k1_enumset1(X2,X3,X4))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X40] : k2_tarski(X40,X40) = k1_tarski(X40) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_28,plain,(
    ! [X41,X42] : k1_enumset1(X41,X41,X42) = k2_tarski(X41,X42) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_29,plain,(
    ! [X38,X39] : k4_xboole_0(X38,k4_xboole_0(X38,X39)) = k3_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_30,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( r2_hidden(X18,X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X15)
        | r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk2_3(X20,X21,X22),X22)
        | ~ r2_hidden(esk2_3(X20,X21,X22),X20)
        | r2_hidden(esk2_3(X20,X21,X22),X21)
        | X22 = k4_xboole_0(X20,X21) )
      & ( r2_hidden(esk2_3(X20,X21,X22),X20)
        | r2_hidden(esk2_3(X20,X21,X22),X22)
        | X22 = k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk2_3(X20,X21,X22),X21)
        | r2_hidden(esk2_3(X20,X21,X22),X22)
        | X22 = k4_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_31,plain,(
    ! [X54,X55] :
      ( ( k4_xboole_0(X54,k1_tarski(X55)) != X54
        | ~ r2_hidden(X55,X54) )
      & ( r2_hidden(X55,X54)
        | k4_xboole_0(X54,k1_tarski(X55)) = X54 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

cnf(c_0_32,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,plain,(
    ! [X32,X33] : r1_tarski(k3_xboole_0(X32,X33),X32) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_35,plain,(
    ! [X36,X37] : k4_xboole_0(X36,k3_xboole_0(X36,X37)) = k4_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k3_enumset1(X2,X2,X2,X3,X4))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk5_0) = k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk6_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_46,plain,(
    ! [X34,X35] : k3_xboole_0(X34,k2_xboole_0(X34,X35)) = X34 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_47,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_49,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_50,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_xboole_0,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) = k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_25]),c_0_40]),c_0_26])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_38]),c_0_39]),c_0_25]),c_0_26])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_58,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | k2_xboole_0(X27,X28) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_59,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_47,c_0_40])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_48,c_0_40])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)) = X1
    | ~ r2_hidden(X2,k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk6_0,k4_xboole_0(esk4_0,X1))
    | r2_hidden(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_57,c_0_40])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_69,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_40]),c_0_40])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_56])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(esk3_0,k3_enumset1(X1,X1,X1,X1,X1)) = esk3_0
    | r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_54])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))) = X1
    | r2_hidden(esk6_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_52])).

cnf(c_0_74,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))) = k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_63])).

cnf(c_0_76,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( k4_xboole_0(esk6_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_54])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(esk3_0,k3_enumset1(X1,X1,X1,X1,X1)) = esk3_0
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_71])).

cnf(c_0_80,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k1_tarski(X4)
    | X1 = k2_tarski(X2,X3)
    | X1 = k2_tarski(X3,X4)
    | X1 = k2_tarski(X2,X4)
    | X1 = k1_enumset1(X2,X3,X4)
    | ~ r1_tarski(X1,k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_81,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))) = k1_xboole_0
    | r2_hidden(esk6_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk6_0,esk6_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_84,plain,
    ( k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_38]),c_0_39]),c_0_25]),c_0_26])).

cnf(c_0_85,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))) = X1
    | ~ r2_hidden(esk6_0,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_73])).

cnf(c_0_86,negated_conjecture,
    ( k4_xboole_0(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_71])).

cnf(c_0_87,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X4,X4,X4,X4,X4)
    | X1 = k3_enumset1(X3,X3,X3,X3,X4)
    | X1 = k3_enumset1(X3,X3,X3,X3,X3)
    | X1 = k3_enumset1(X2,X2,X2,X3,X4)
    | X1 = k3_enumset1(X2,X2,X2,X2,X4)
    | X1 = k3_enumset1(X2,X2,X2,X2,X3)
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k3_enumset1(X2,X2,X2,X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_88,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r2_hidden(esk6_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(X1,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))
    | ~ r2_hidden(X1,k4_xboole_0(esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))) != X1
    | ~ r2_hidden(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_52])).

cnf(c_0_91,negated_conjecture,
    ( k4_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_45])])).

cnf(c_0_92,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k4_xboole_0(esk6_0,esk6_0)
    | k4_xboole_0(esk6_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_87,c_0_83])).

cnf(c_0_93,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ r2_hidden(esk6_0,k4_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk6_0,esk6_0),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))) = k4_xboole_0(esk6_0,esk6_0)
    | r2_hidden(esk6_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_73])).

cnf(c_0_95,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_96,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_97,plain,(
    ! [X24] : k3_xboole_0(X24,X24) = X24 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_98,negated_conjecture,
    ( k4_xboole_0(esk6_0,esk6_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k4_xboole_0(esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ r2_hidden(esk6_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_82])).

cnf(c_0_100,plain,
    ( k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)) = X1
    | r2_hidden(X2,k4_xboole_0(X1,X3))
    | r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_55,c_0_54])).

cnf(c_0_101,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk6_0,esk6_0),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))) = k4_xboole_0(esk6_0,esk6_0) ),
    inference(sr,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_102,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_96])).

cnf(c_0_103,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( k4_xboole_0(esk6_0,esk6_0) = k1_xboole_0
    | r2_hidden(X1,k4_xboole_0(esk6_0,esk6_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_98])).

cnf(c_0_105,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r2_hidden(esk6_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_52]),c_0_82])])).

cnf(c_0_106,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k4_xboole_0(esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_101])).

cnf(c_0_107,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk1_2(X1,X2),k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_102])).

cnf(c_0_108,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_103,c_0_40])).

cnf(c_0_109,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k4_xboole_0(esk6_0,esk6_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_106])).

cnf(c_0_110,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),X2) = X2
    | ~ r2_hidden(esk1_2(k4_xboole_0(X1,X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_111,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_109]),c_0_82])])).

cnf(c_0_112,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_102])).

cnf(c_0_113,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_112]),c_0_111])).

cnf(c_0_114,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_113])).

cnf(c_0_115,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_116,plain,(
    ! [X29,X30,X31] : k3_xboole_0(k3_xboole_0(X29,X30),X31) = k3_xboole_0(X29,k3_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_117,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_113])).

cnf(c_0_118,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_119,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k4_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_45])).

cnf(c_0_120,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_121,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk2_3(k1_xboole_0,X2,X1),k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_117])).

cnf(c_0_122,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_118])).

cnf(c_0_123,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk3_0),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))) = k4_xboole_0(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_54]),c_0_52])).

cnf(c_0_124,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_125,negated_conjecture,
    ( k4_xboole_0(X1,X1) = k1_xboole_0
    | ~ r2_hidden(esk2_3(k1_xboole_0,X2,k4_xboole_0(X1,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_108])).

cnf(c_0_126,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(X3,X4)
    | r2_hidden(esk2_3(X3,X4,k4_xboole_0(X1,X2)),X3)
    | r2_hidden(esk2_3(X3,X4,k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_122,c_0_115])).

cnf(c_0_127,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_33])).

cnf(c_0_128,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk3_0),k4_xboole_0(X1,esk3_0)) = k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(X1,esk3_0))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_123]),c_0_124])).

cnf(c_0_129,negated_conjecture,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_113])]),c_0_114])).

cnf(c_0_130,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_127])).

cnf(c_0_131,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) != k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_132,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_124])).

cnf(c_0_133,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(X1,esk3_0))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_134,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_124])).

cnf(c_0_135,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k4_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_130])).

cnf(c_0_136,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)) != k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_131,c_0_38]),c_0_39]),c_0_25]),c_0_40]),c_0_26])).

cnf(c_0_137,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)),esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_132,c_0_133])).

cnf(c_0_138,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_108,c_0_129])).

cnf(c_0_139,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))) = k4_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_108]),c_0_60]),c_0_108])).

cnf(c_0_140,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) != k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_136,c_0_52])).

cnf(c_0_141,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_137]),c_0_138]),c_0_139]),c_0_140]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:35:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.44/0.61  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.44/0.61  # and selection function SelectCQArNTNpEqFirst.
% 0.44/0.61  #
% 0.44/0.61  # Preprocessing time       : 0.028 s
% 0.44/0.61  # Presaturation interreduction done
% 0.44/0.61  
% 0.44/0.61  # Proof found!
% 0.44/0.61  # SZS status Theorem
% 0.44/0.61  # SZS output start CNFRefutation
% 0.44/0.61  fof(t148_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 0.44/0.61  fof(t142_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r1_tarski(X4,k1_enumset1(X1,X2,X3))<=>~((((((((X4!=k1_xboole_0&X4!=k1_tarski(X1))&X4!=k1_tarski(X2))&X4!=k1_tarski(X3))&X4!=k2_tarski(X1,X2))&X4!=k2_tarski(X2,X3))&X4!=k2_tarski(X1,X3))&X4!=k1_enumset1(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 0.44/0.61  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.44/0.61  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.44/0.61  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.44/0.61  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.44/0.61  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.44/0.61  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.44/0.61  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.44/0.61  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.44/0.61  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.44/0.61  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.44/0.61  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.44/0.61  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.44/0.61  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.44/0.61  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.44/0.61  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.44/0.61  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.44/0.61  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4))), inference(assume_negation,[status(cth)],[t148_zfmisc_1])).
% 0.44/0.61  fof(c_0_19, plain, ![X50, X51, X52, X53]:((~r1_tarski(X53,k1_enumset1(X50,X51,X52))|(X53=k1_xboole_0|X53=k1_tarski(X50)|X53=k1_tarski(X51)|X53=k1_tarski(X52)|X53=k2_tarski(X50,X51)|X53=k2_tarski(X51,X52)|X53=k2_tarski(X50,X52)|X53=k1_enumset1(X50,X51,X52)))&((((((((X53!=k1_xboole_0|r1_tarski(X53,k1_enumset1(X50,X51,X52)))&(X53!=k1_tarski(X50)|r1_tarski(X53,k1_enumset1(X50,X51,X52))))&(X53!=k1_tarski(X51)|r1_tarski(X53,k1_enumset1(X50,X51,X52))))&(X53!=k1_tarski(X52)|r1_tarski(X53,k1_enumset1(X50,X51,X52))))&(X53!=k2_tarski(X50,X51)|r1_tarski(X53,k1_enumset1(X50,X51,X52))))&(X53!=k2_tarski(X51,X52)|r1_tarski(X53,k1_enumset1(X50,X51,X52))))&(X53!=k2_tarski(X50,X52)|r1_tarski(X53,k1_enumset1(X50,X51,X52))))&(X53!=k1_enumset1(X50,X51,X52)|r1_tarski(X53,k1_enumset1(X50,X51,X52))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).
% 0.44/0.61  fof(c_0_20, plain, ![X43, X44, X45]:k2_enumset1(X43,X43,X44,X45)=k1_enumset1(X43,X44,X45), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.44/0.61  fof(c_0_21, plain, ![X46, X47, X48, X49]:k3_enumset1(X46,X46,X47,X48,X49)=k2_enumset1(X46,X47,X48,X49), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.44/0.61  fof(c_0_22, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk1_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk1_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.44/0.61  fof(c_0_23, negated_conjecture, (((r1_tarski(esk3_0,esk4_0)&k3_xboole_0(esk4_0,esk5_0)=k1_tarski(esk6_0))&r2_hidden(esk6_0,esk3_0))&k3_xboole_0(esk3_0,esk5_0)!=k1_tarski(esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.44/0.61  cnf(c_0_24, plain, (r1_tarski(X1,k1_enumset1(X2,X3,X4))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.44/0.61  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.44/0.61  cnf(c_0_26, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.44/0.61  fof(c_0_27, plain, ![X40]:k2_tarski(X40,X40)=k1_tarski(X40), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.44/0.61  fof(c_0_28, plain, ![X41, X42]:k1_enumset1(X41,X41,X42)=k2_tarski(X41,X42), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.44/0.61  fof(c_0_29, plain, ![X38, X39]:k4_xboole_0(X38,k4_xboole_0(X38,X39))=k3_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.44/0.61  fof(c_0_30, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:((((r2_hidden(X18,X15)|~r2_hidden(X18,X17)|X17!=k4_xboole_0(X15,X16))&(~r2_hidden(X18,X16)|~r2_hidden(X18,X17)|X17!=k4_xboole_0(X15,X16)))&(~r2_hidden(X19,X15)|r2_hidden(X19,X16)|r2_hidden(X19,X17)|X17!=k4_xboole_0(X15,X16)))&((~r2_hidden(esk2_3(X20,X21,X22),X22)|(~r2_hidden(esk2_3(X20,X21,X22),X20)|r2_hidden(esk2_3(X20,X21,X22),X21))|X22=k4_xboole_0(X20,X21))&((r2_hidden(esk2_3(X20,X21,X22),X20)|r2_hidden(esk2_3(X20,X21,X22),X22)|X22=k4_xboole_0(X20,X21))&(~r2_hidden(esk2_3(X20,X21,X22),X21)|r2_hidden(esk2_3(X20,X21,X22),X22)|X22=k4_xboole_0(X20,X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.44/0.61  fof(c_0_31, plain, ![X54, X55]:((k4_xboole_0(X54,k1_tarski(X55))!=X54|~r2_hidden(X55,X54))&(r2_hidden(X55,X54)|k4_xboole_0(X54,k1_tarski(X55))=X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.44/0.61  cnf(c_0_32, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.44/0.61  cnf(c_0_33, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.44/0.61  fof(c_0_34, plain, ![X32, X33]:r1_tarski(k3_xboole_0(X32,X33),X32), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.44/0.61  fof(c_0_35, plain, ![X36, X37]:k4_xboole_0(X36,k3_xboole_0(X36,X37))=k4_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.44/0.61  cnf(c_0_36, plain, (r1_tarski(X1,k3_enumset1(X2,X2,X2,X3,X4))|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.44/0.61  cnf(c_0_37, negated_conjecture, (k3_xboole_0(esk4_0,esk5_0)=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.44/0.61  cnf(c_0_38, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.44/0.61  cnf(c_0_39, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.44/0.61  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.44/0.61  cnf(c_0_41, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.44/0.61  cnf(c_0_42, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.44/0.61  cnf(c_0_43, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.44/0.61  cnf(c_0_44, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.44/0.61  cnf(c_0_45, negated_conjecture, (r2_hidden(esk6_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.44/0.61  fof(c_0_46, plain, ![X34, X35]:k3_xboole_0(X34,k2_xboole_0(X34,X35))=X34, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.44/0.61  cnf(c_0_47, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.44/0.61  cnf(c_0_48, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.44/0.61  fof(c_0_49, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.44/0.61  fof(c_0_50, plain, ![X5, X6]:(~r2_hidden(X5,X6)|~r2_hidden(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.44/0.61  cnf(c_0_51, plain, (r1_tarski(k1_xboole_0,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[c_0_36])).
% 0.44/0.61  cnf(c_0_52, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))=k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_25]), c_0_40]), c_0_26])).
% 0.44/0.61  cnf(c_0_53, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_41])).
% 0.44/0.61  cnf(c_0_54, plain, (k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_38]), c_0_39]), c_0_25]), c_0_26])).
% 0.44/0.61  cnf(c_0_55, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_43])).
% 0.44/0.61  cnf(c_0_56, negated_conjecture, (r2_hidden(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.44/0.61  cnf(c_0_57, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.44/0.61  fof(c_0_58, plain, ![X27, X28]:(~r1_tarski(X27,X28)|k2_xboole_0(X27,X28)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.44/0.61  cnf(c_0_59, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_47, c_0_40])).
% 0.44/0.61  cnf(c_0_60, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_48, c_0_40])).
% 0.44/0.61  cnf(c_0_61, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.44/0.61  cnf(c_0_62, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.44/0.61  cnf(c_0_63, negated_conjecture, (r1_tarski(k1_xboole_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.44/0.61  cnf(c_0_64, plain, (k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))=X1|~r2_hidden(X2,k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.44/0.61  cnf(c_0_65, negated_conjecture, (r2_hidden(esk6_0,k4_xboole_0(esk4_0,X1))|r2_hidden(esk6_0,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.44/0.61  cnf(c_0_66, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_57, c_0_40])).
% 0.44/0.61  cnf(c_0_67, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.44/0.61  cnf(c_0_68, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.44/0.61  cnf(c_0_69, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_40]), c_0_40])).
% 0.44/0.61  cnf(c_0_70, negated_conjecture, (~r2_hidden(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_62, c_0_56])).
% 0.44/0.61  cnf(c_0_71, negated_conjecture, (k4_xboole_0(esk3_0,k3_enumset1(X1,X1,X1,X1,X1))=esk3_0|r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_54])).
% 0.44/0.61  cnf(c_0_72, negated_conjecture, (r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_63])).
% 0.44/0.61  cnf(c_0_73, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))=X1|r2_hidden(esk6_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_52])).
% 0.44/0.61  cnf(c_0_74, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_60, c_0_66])).
% 0.44/0.61  cnf(c_0_75, negated_conjecture, (k2_xboole_0(k1_xboole_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_67, c_0_63])).
% 0.44/0.61  cnf(c_0_76, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.44/0.61  cnf(c_0_77, negated_conjecture, (k4_xboole_0(esk6_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=esk6_0), inference(spm,[status(thm)],[c_0_70, c_0_54])).
% 0.44/0.61  cnf(c_0_78, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.44/0.61  cnf(c_0_79, negated_conjecture, (k4_xboole_0(esk3_0,k3_enumset1(X1,X1,X1,X1,X1))=esk3_0|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_62, c_0_71])).
% 0.44/0.61  cnf(c_0_80, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k1_tarski(X4)|X1=k2_tarski(X2,X3)|X1=k2_tarski(X3,X4)|X1=k2_tarski(X2,X4)|X1=k1_enumset1(X2,X3,X4)|~r1_tarski(X1,k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.44/0.61  cnf(c_0_81, negated_conjecture, (k4_xboole_0(k1_xboole_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))=k1_xboole_0|r2_hidden(esk6_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.44/0.61  cnf(c_0_82, negated_conjecture, (k4_xboole_0(k1_xboole_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))=k4_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.44/0.61  cnf(c_0_83, negated_conjecture, (r1_tarski(k4_xboole_0(esk6_0,esk6_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.44/0.61  cnf(c_0_84, plain, (k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_38]), c_0_39]), c_0_25]), c_0_26])).
% 0.44/0.61  cnf(c_0_85, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))=X1|~r2_hidden(esk6_0,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_53, c_0_73])).
% 0.44/0.61  cnf(c_0_86, negated_conjecture, (k4_xboole_0(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_79, c_0_71])).
% 0.44/0.61  cnf(c_0_87, plain, (X1=k1_xboole_0|X1=k3_enumset1(X4,X4,X4,X4,X4)|X1=k3_enumset1(X3,X3,X3,X3,X4)|X1=k3_enumset1(X3,X3,X3,X3,X3)|X1=k3_enumset1(X2,X2,X2,X3,X4)|X1=k3_enumset1(X2,X2,X2,X2,X4)|X1=k3_enumset1(X2,X2,X2,X2,X3)|X1=k3_enumset1(X2,X2,X2,X2,X2)|~r1_tarski(X1,k3_enumset1(X2,X2,X2,X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 0.44/0.61  cnf(c_0_88, negated_conjecture, (k4_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0|r2_hidden(esk6_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))), inference(rw,[status(thm)],[c_0_81, c_0_82])).
% 0.44/0.61  cnf(c_0_89, negated_conjecture, (r2_hidden(X1,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))|~r2_hidden(X1,k4_xboole_0(esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_32, c_0_83])).
% 0.44/0.61  cnf(c_0_90, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))!=X1|~r2_hidden(esk6_0,X1)), inference(spm,[status(thm)],[c_0_84, c_0_52])).
% 0.44/0.61  cnf(c_0_91, negated_conjecture, (k4_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_45])])).
% 0.44/0.61  cnf(c_0_92, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k4_xboole_0(esk6_0,esk6_0)|k4_xboole_0(esk6_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_87, c_0_83])).
% 0.44/0.61  cnf(c_0_93, negated_conjecture, (k4_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0|~r2_hidden(esk6_0,k4_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))))), inference(spm,[status(thm)],[c_0_53, c_0_88])).
% 0.44/0.61  cnf(c_0_94, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk6_0,esk6_0),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))=k4_xboole_0(esk6_0,esk6_0)|r2_hidden(esk6_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_89, c_0_73])).
% 0.44/0.61  cnf(c_0_95, negated_conjecture, (~r2_hidden(esk6_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.44/0.61  cnf(c_0_96, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.44/0.61  fof(c_0_97, plain, ![X24]:k3_xboole_0(X24,X24)=X24, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.44/0.61  cnf(c_0_98, negated_conjecture, (k4_xboole_0(esk6_0,esk6_0)=k1_xboole_0|r1_tarski(k1_xboole_0,k4_xboole_0(esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_51, c_0_92])).
% 0.44/0.61  cnf(c_0_99, negated_conjecture, (k4_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0|~r2_hidden(esk6_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_93, c_0_82])).
% 0.44/0.61  cnf(c_0_100, plain, (k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))=X1|r2_hidden(X2,k4_xboole_0(X1,X3))|r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_55, c_0_54])).
% 0.44/0.61  cnf(c_0_101, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk6_0,esk6_0),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))=k4_xboole_0(esk6_0,esk6_0)), inference(sr,[status(thm)],[c_0_94, c_0_95])).
% 0.44/0.61  cnf(c_0_102, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_67, c_0_96])).
% 0.44/0.61  cnf(c_0_103, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.44/0.61  cnf(c_0_104, negated_conjecture, (k4_xboole_0(esk6_0,esk6_0)=k1_xboole_0|r2_hidden(X1,k4_xboole_0(esk6_0,esk6_0))|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_98])).
% 0.44/0.61  cnf(c_0_105, negated_conjecture, (k4_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0|r2_hidden(esk6_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_52]), c_0_82])])).
% 0.44/0.61  cnf(c_0_106, negated_conjecture, (~r2_hidden(esk6_0,k4_xboole_0(esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_90, c_0_101])).
% 0.44/0.61  cnf(c_0_107, plain, (k2_xboole_0(X1,X2)=X2|~r2_hidden(esk1_2(X1,X2),k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_53, c_0_102])).
% 0.44/0.61  cnf(c_0_108, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_103, c_0_40])).
% 0.44/0.61  cnf(c_0_109, negated_conjecture, (k4_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0|k4_xboole_0(esk6_0,esk6_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_106])).
% 0.44/0.61  cnf(c_0_110, plain, (k2_xboole_0(k4_xboole_0(X1,X1),X2)=X2|~r2_hidden(esk1_2(k4_xboole_0(X1,X1),X2),X1)), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 0.44/0.61  cnf(c_0_111, negated_conjecture, (k4_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_109]), c_0_82])])).
% 0.44/0.61  cnf(c_0_112, negated_conjecture, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_102])).
% 0.44/0.61  cnf(c_0_113, negated_conjecture, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_112]), c_0_111])).
% 0.44/0.61  cnf(c_0_114, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_84, c_0_113])).
% 0.44/0.61  cnf(c_0_115, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.44/0.61  fof(c_0_116, plain, ![X29, X30, X31]:k3_xboole_0(k3_xboole_0(X29,X30),X31)=k3_xboole_0(X29,k3_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.44/0.61  cnf(c_0_117, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_113])).
% 0.44/0.61  cnf(c_0_118, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.44/0.61  cnf(c_0_119, negated_conjecture, (~r2_hidden(esk6_0,k4_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_53, c_0_45])).
% 0.44/0.61  cnf(c_0_120, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_116])).
% 0.44/0.61  cnf(c_0_121, negated_conjecture, (X1=k1_xboole_0|~r2_hidden(esk2_3(k1_xboole_0,X2,X1),k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_53, c_0_117])).
% 0.44/0.61  cnf(c_0_122, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_118])).
% 0.44/0.61  cnf(c_0_123, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk3_0),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))=k4_xboole_0(X1,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_54]), c_0_52])).
% 0.44/0.61  cnf(c_0_124, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 0.44/0.61  cnf(c_0_125, negated_conjecture, (k4_xboole_0(X1,X1)=k1_xboole_0|~r2_hidden(esk2_3(k1_xboole_0,X2,k4_xboole_0(X1,X1)),X1)), inference(spm,[status(thm)],[c_0_121, c_0_108])).
% 0.44/0.61  cnf(c_0_126, plain, (k4_xboole_0(X1,X2)=k4_xboole_0(X3,X4)|r2_hidden(esk2_3(X3,X4,k4_xboole_0(X1,X2)),X3)|r2_hidden(esk2_3(X3,X4,k4_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_122, c_0_115])).
% 0.44/0.61  cnf(c_0_127, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_67, c_0_33])).
% 0.44/0.61  cnf(c_0_128, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk3_0),k4_xboole_0(X1,esk3_0))=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(X1,esk3_0)))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_123]), c_0_124])).
% 0.44/0.61  cnf(c_0_129, negated_conjecture, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_113])]), c_0_114])).
% 0.44/0.61  cnf(c_0_130, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_66, c_0_127])).
% 0.44/0.61  cnf(c_0_131, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)!=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.44/0.61  cnf(c_0_132, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)))))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_60, c_0_124])).
% 0.44/0.61  cnf(c_0_133, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(X1,esk3_0)))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_128, c_0_129])).
% 0.44/0.61  cnf(c_0_134, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_60, c_0_124])).
% 0.44/0.61  cnf(c_0_135, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k4_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_60, c_0_130])).
% 0.44/0.61  cnf(c_0_136, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))!=k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_131, c_0_38]), c_0_39]), c_0_25]), c_0_40]), c_0_26])).
% 0.44/0.61  cnf(c_0_137, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)),esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_132, c_0_133])).
% 0.44/0.61  cnf(c_0_138, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_108, c_0_129])).
% 0.44/0.61  cnf(c_0_139, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1)))=k4_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_108]), c_0_60]), c_0_108])).
% 0.44/0.61  cnf(c_0_140, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))!=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))), inference(rw,[status(thm)],[c_0_136, c_0_52])).
% 0.44/0.61  cnf(c_0_141, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_137]), c_0_138]), c_0_139]), c_0_140]), ['proof']).
% 0.44/0.61  # SZS output end CNFRefutation
% 0.44/0.61  # Proof object total steps             : 142
% 0.44/0.61  # Proof object clause steps            : 105
% 0.44/0.61  # Proof object formula steps           : 37
% 0.44/0.61  # Proof object conjectures             : 59
% 0.44/0.61  # Proof object clause conjectures      : 56
% 0.44/0.61  # Proof object formula conjectures     : 3
% 0.44/0.61  # Proof object initial clauses used    : 27
% 0.44/0.61  # Proof object initial formulas used   : 18
% 0.44/0.61  # Proof object generating inferences   : 57
% 0.44/0.61  # Proof object simplifying inferences  : 87
% 0.44/0.61  # Training examples: 0 positive, 0 negative
% 0.44/0.61  # Parsed axioms                        : 19
% 0.44/0.61  # Removed by relevancy pruning/SinE    : 0
% 0.44/0.61  # Initial clauses                      : 40
% 0.44/0.61  # Removed in clause preprocessing      : 5
% 0.44/0.61  # Initial clauses in saturation        : 35
% 0.44/0.61  # Processed clauses                    : 2204
% 0.44/0.61  # ...of these trivial                  : 108
% 0.44/0.61  # ...subsumed                          : 1389
% 0.44/0.61  # ...remaining for further processing  : 707
% 0.44/0.61  # Other redundant clauses eliminated   : 13
% 0.44/0.61  # Clauses deleted for lack of memory   : 0
% 0.44/0.61  # Backward-subsumed                    : 13
% 0.44/0.61  # Backward-rewritten                   : 329
% 0.44/0.61  # Generated clauses                    : 16745
% 0.44/0.61  # ...of the previous two non-trivial   : 13491
% 0.44/0.61  # Contextual simplify-reflections      : 1
% 0.44/0.61  # Paramodulations                      : 16714
% 0.44/0.61  # Factorizations                       : 17
% 0.44/0.61  # Equation resolutions                 : 13
% 0.44/0.61  # Propositional unsat checks           : 0
% 0.44/0.61  #    Propositional check models        : 0
% 0.44/0.61  #    Propositional check unsatisfiable : 0
% 0.44/0.61  #    Propositional clauses             : 0
% 0.44/0.61  #    Propositional clauses after purity: 0
% 0.44/0.61  #    Propositional unsat core size     : 0
% 0.44/0.61  #    Propositional preprocessing time  : 0.000
% 0.44/0.61  #    Propositional encoding time       : 0.000
% 0.44/0.61  #    Propositional solver time         : 0.000
% 0.44/0.61  #    Success case prop preproc time    : 0.000
% 0.44/0.61  #    Success case prop encoding time   : 0.000
% 0.44/0.61  #    Success case prop solver time     : 0.000
% 0.44/0.61  # Current number of processed clauses  : 318
% 0.44/0.61  #    Positive orientable unit clauses  : 100
% 0.44/0.61  #    Positive unorientable unit clauses: 3
% 0.44/0.61  #    Negative unit clauses             : 61
% 0.44/0.61  #    Non-unit-clauses                  : 154
% 0.44/0.61  # Current number of unprocessed clauses: 11218
% 0.44/0.61  # ...number of literals in the above   : 21272
% 0.44/0.61  # Current number of archived formulas  : 0
% 0.44/0.61  # Current number of archived clauses   : 381
% 0.44/0.61  # Clause-clause subsumption calls (NU) : 8896
% 0.44/0.61  # Rec. Clause-clause subsumption calls : 7725
% 0.44/0.61  # Non-unit clause-clause subsumptions  : 411
% 0.44/0.61  # Unit Clause-clause subsumption calls : 3342
% 0.44/0.61  # Rewrite failures with RHS unbound    : 0
% 0.44/0.61  # BW rewrite match attempts            : 1332
% 0.44/0.61  # BW rewrite match successes           : 181
% 0.44/0.61  # Condensation attempts                : 0
% 0.44/0.61  # Condensation successes               : 0
% 0.44/0.61  # Termbank termtop insertions          : 325514
% 0.44/0.61  
% 0.44/0.61  # -------------------------------------------------
% 0.44/0.61  # User time                : 0.246 s
% 0.44/0.61  # System time              : 0.017 s
% 0.44/0.61  # Total time               : 0.263 s
% 0.44/0.61  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
