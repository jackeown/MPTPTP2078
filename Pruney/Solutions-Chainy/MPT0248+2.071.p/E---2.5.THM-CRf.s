%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:48 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  114 (4409 expanded)
%              Number of clauses        :   69 (1663 expanded)
%              Number of leaves         :   22 (1352 expanded)
%              Depth                    :   17
%              Number of atoms          :  219 (5795 expanded)
%              Number of equality atoms :  140 (5274 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_22,plain,(
    ! [X75,X76] : k3_tarski(k2_tarski(X75,X76)) = k2_xboole_0(X75,X76) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X46,X47] : k1_enumset1(X46,X46,X47) = k2_tarski(X46,X47) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X28,X29] : r1_tarski(X28,k2_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_26,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X48,X49,X50] : k2_enumset1(X48,X48,X49,X50) = k1_enumset1(X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_29,plain,(
    ! [X51,X52,X53,X54] : k3_enumset1(X51,X51,X52,X53,X54) = k2_enumset1(X51,X52,X53,X54) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_30,plain,(
    ! [X55,X56,X57,X58,X59] : k4_enumset1(X55,X55,X56,X57,X58,X59) = k3_enumset1(X55,X56,X57,X58,X59) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_31,plain,(
    ! [X60,X61,X62,X63,X64,X65] : k5_enumset1(X60,X60,X61,X62,X63,X64,X65) = k4_enumset1(X60,X61,X62,X63,X64,X65) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_32,plain,(
    ! [X66,X67,X68,X69,X70,X71,X72] : k6_enumset1(X66,X66,X67,X68,X69,X70,X71,X72) = k5_enumset1(X66,X67,X68,X69,X70,X71,X72) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_33,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0)
    & ( esk5_0 != k1_tarski(esk4_0)
      | esk6_0 != k1_tarski(esk4_0) )
    & ( esk5_0 != k1_xboole_0
      | esk6_0 != k1_tarski(esk4_0) )
    & ( esk5_0 != k1_tarski(esk4_0)
      | esk6_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_34,plain,(
    ! [X45] : k2_tarski(X45,X45) = k1_tarski(X45) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_44,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42,X43] :
      ( ( ~ r2_hidden(X39,X38)
        | X39 = X36
        | X39 = X37
        | X38 != k2_tarski(X36,X37) )
      & ( X40 != X36
        | r2_hidden(X40,X38)
        | X38 != k2_tarski(X36,X37) )
      & ( X40 != X37
        | r2_hidden(X40,X38)
        | X38 != k2_tarski(X36,X37) )
      & ( esk3_3(X41,X42,X43) != X41
        | ~ r2_hidden(esk3_3(X41,X42,X43),X43)
        | X43 = k2_tarski(X41,X42) )
      & ( esk3_3(X41,X42,X43) != X42
        | ~ r2_hidden(esk3_3(X41,X42,X43),X43)
        | X43 = k2_tarski(X41,X42) )
      & ( r2_hidden(esk3_3(X41,X42,X43),X43)
        | esk3_3(X41,X42,X43) = X41
        | esk3_3(X41,X42,X43) = X42
        | X43 = k2_tarski(X41,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_45,plain,(
    ! [X14,X15,X16,X17,X18] :
      ( ( ~ r1_tarski(X14,X15)
        | ~ r2_hidden(X16,X14)
        | r2_hidden(X16,X15) )
      & ( r2_hidden(esk2_2(X17,X18),X17)
        | r1_tarski(X17,X18) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | r1_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_27]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41])).

fof(c_0_48,plain,(
    ! [X34,X35] : k3_xboole_0(X34,X35) = k5_xboole_0(k5_xboole_0(X34,X35),k2_xboole_0(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_49,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk5_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_52,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v1_xboole_0(X10)
        | ~ r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_1(X12),X12)
        | v1_xboole_0(X12) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_53,plain,(
    ! [X26,X27] : r1_tarski(k3_xboole_0(X26,X27),X26) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_55,plain,(
    ! [X21] : k3_xboole_0(X21,X21) = X21 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_56,plain,(
    ! [X20] : k2_xboole_0(X20,X20) = X20 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_57,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_27]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(X1,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_60,plain,(
    ! [X73,X74] :
      ( ( ~ r1_tarski(X73,k1_tarski(X74))
        | X73 = k1_xboole_0
        | X73 = k1_tarski(X74) )
      & ( X73 != k1_xboole_0
        | r1_tarski(X73,k1_tarski(X74)) )
      & ( X73 != k1_tarski(X74)
        | r1_tarski(X73,k1_tarski(X74)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_61,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_36]),c_0_37]),c_0_38])).

fof(c_0_63,plain,(
    ! [X30,X31,X32] : k5_xboole_0(k5_xboole_0(X30,X31),X32) = k5_xboole_0(X30,k5_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_65,plain,(
    ! [X33] : k5_xboole_0(X33,X33) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_66,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk1_1(esk5_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))
    | v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_71,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_62]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_75,negated_conjecture,
    ( esk1_1(esk5_0) = esk4_0
    | v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_43]),c_0_43]),c_0_27]),c_0_27]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41])).

cnf(c_0_77,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X1) ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

fof(c_0_78,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_79,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73]),c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( esk5_0 != k1_tarski(esk4_0)
    | esk6_0 != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_81,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k2_xboole_0(X24,X25) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_82,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk5_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_76,c_0_51])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_47])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_73]),c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( esk5_0 != k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)
    | esk6_0 != k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_43]),c_0_43]),c_0_27]),c_0_27]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41])).

cnf(c_0_89,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_91,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_92,negated_conjecture,
    ( esk5_0 != k1_tarski(esk4_0)
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_93,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | X1 = esk5_0
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_84])).

cnf(c_0_94,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(esk6_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_84]),c_0_86]),c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 != esk5_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_84])).

cnf(c_0_96,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_97,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_99,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | esk6_0 != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_100,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk5_0 != k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_43]),c_0_27]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_101,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95])).

cnf(c_0_102,plain,
    ( r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_43]),c_0_27]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_103,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1)) = X1
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | esk6_0 != k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_43]),c_0_27]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_105,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_84])).

cnf(c_0_106,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk6_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_103])).

cnf(c_0_108,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_105])])).

cnf(c_0_109,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_106])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(esk4_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_105]),c_0_108])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(esk4_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_112,negated_conjecture,
    ( esk4_0 = X1 ),
    inference(spm,[status(thm)],[c_0_67,c_0_111])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_112]),c_0_112])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:10:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.12/0.39  # and selection function GSelectMinInfpos.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.016 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.12/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.39  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.12/0.39  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.12/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.12/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.12/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.12/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.39  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.12/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.39  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.12/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.12/0.39  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.12/0.39  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.12/0.39  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.12/0.39  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.12/0.39  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.12/0.39  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.12/0.39  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.12/0.39  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.12/0.39  fof(c_0_22, plain, ![X75, X76]:k3_tarski(k2_tarski(X75,X76))=k2_xboole_0(X75,X76), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.12/0.39  fof(c_0_23, plain, ![X46, X47]:k1_enumset1(X46,X46,X47)=k2_tarski(X46,X47), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.39  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.12/0.39  fof(c_0_25, plain, ![X28, X29]:r1_tarski(X28,k2_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.12/0.39  cnf(c_0_26, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.39  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.39  fof(c_0_28, plain, ![X48, X49, X50]:k2_enumset1(X48,X48,X49,X50)=k1_enumset1(X48,X49,X50), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.39  fof(c_0_29, plain, ![X51, X52, X53, X54]:k3_enumset1(X51,X51,X52,X53,X54)=k2_enumset1(X51,X52,X53,X54), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.39  fof(c_0_30, plain, ![X55, X56, X57, X58, X59]:k4_enumset1(X55,X55,X56,X57,X58,X59)=k3_enumset1(X55,X56,X57,X58,X59), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.12/0.39  fof(c_0_31, plain, ![X60, X61, X62, X63, X64, X65]:k5_enumset1(X60,X60,X61,X62,X63,X64,X65)=k4_enumset1(X60,X61,X62,X63,X64,X65), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.12/0.39  fof(c_0_32, plain, ![X66, X67, X68, X69, X70, X71, X72]:k6_enumset1(X66,X66,X67,X68,X69,X70,X71,X72)=k5_enumset1(X66,X67,X68,X69,X70,X71,X72), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.12/0.39  fof(c_0_33, negated_conjecture, (((k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)&(esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_tarski(esk4_0)))&(esk5_0!=k1_xboole_0|esk6_0!=k1_tarski(esk4_0)))&(esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.12/0.39  fof(c_0_34, plain, ![X45]:k2_tarski(X45,X45)=k1_tarski(X45), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.39  cnf(c_0_35, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.39  cnf(c_0_36, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.39  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.39  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.39  cnf(c_0_39, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.39  cnf(c_0_40, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.39  cnf(c_0_41, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.39  cnf(c_0_42, negated_conjecture, (k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.39  cnf(c_0_43, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.39  fof(c_0_44, plain, ![X36, X37, X38, X39, X40, X41, X42, X43]:(((~r2_hidden(X39,X38)|(X39=X36|X39=X37)|X38!=k2_tarski(X36,X37))&((X40!=X36|r2_hidden(X40,X38)|X38!=k2_tarski(X36,X37))&(X40!=X37|r2_hidden(X40,X38)|X38!=k2_tarski(X36,X37))))&(((esk3_3(X41,X42,X43)!=X41|~r2_hidden(esk3_3(X41,X42,X43),X43)|X43=k2_tarski(X41,X42))&(esk3_3(X41,X42,X43)!=X42|~r2_hidden(esk3_3(X41,X42,X43),X43)|X43=k2_tarski(X41,X42)))&(r2_hidden(esk3_3(X41,X42,X43),X43)|(esk3_3(X41,X42,X43)=X41|esk3_3(X41,X42,X43)=X42)|X43=k2_tarski(X41,X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.12/0.39  fof(c_0_45, plain, ![X14, X15, X16, X17, X18]:((~r1_tarski(X14,X15)|(~r2_hidden(X16,X14)|r2_hidden(X16,X15)))&((r2_hidden(esk2_2(X17,X18),X17)|r1_tarski(X17,X18))&(~r2_hidden(esk2_2(X17,X18),X18)|r1_tarski(X17,X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.39  cnf(c_0_46, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.12/0.39  cnf(c_0_47, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_27]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41])).
% 0.12/0.39  fof(c_0_48, plain, ![X34, X35]:k3_xboole_0(X34,X35)=k5_xboole_0(k5_xboole_0(X34,X35),k2_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.12/0.39  cnf(c_0_49, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.12/0.39  cnf(c_0_50, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.12/0.39  cnf(c_0_51, negated_conjecture, (r1_tarski(esk5_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.12/0.39  fof(c_0_52, plain, ![X10, X11, X12]:((~v1_xboole_0(X10)|~r2_hidden(X11,X10))&(r2_hidden(esk1_1(X12),X12)|v1_xboole_0(X12))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.12/0.39  fof(c_0_53, plain, ![X26, X27]:r1_tarski(k3_xboole_0(X26,X27),X26), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.12/0.39  cnf(c_0_54, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.39  fof(c_0_55, plain, ![X21]:k3_xboole_0(X21,X21)=X21, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.12/0.39  fof(c_0_56, plain, ![X20]:k2_xboole_0(X20,X20)=X20, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.12/0.39  cnf(c_0_57, plain, (X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_27]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.12/0.39  cnf(c_0_58, negated_conjecture, (r2_hidden(X1,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.12/0.39  cnf(c_0_59, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.12/0.39  fof(c_0_60, plain, ![X73, X74]:((~r1_tarski(X73,k1_tarski(X74))|(X73=k1_xboole_0|X73=k1_tarski(X74)))&((X73!=k1_xboole_0|r1_tarski(X73,k1_tarski(X74)))&(X73!=k1_tarski(X74)|r1_tarski(X73,k1_tarski(X74))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.12/0.39  cnf(c_0_61, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.12/0.39  cnf(c_0_62, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_36]), c_0_37]), c_0_38])).
% 0.12/0.39  fof(c_0_63, plain, ![X30, X31, X32]:k5_xboole_0(k5_xboole_0(X30,X31),X32)=k5_xboole_0(X30,k5_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.12/0.39  cnf(c_0_64, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.12/0.39  fof(c_0_65, plain, ![X33]:k5_xboole_0(X33,X33)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.12/0.39  cnf(c_0_66, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.12/0.39  cnf(c_0_67, plain, (X1=X2|X1=X3|~r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_57])).
% 0.12/0.39  cnf(c_0_68, negated_conjecture, (r2_hidden(esk1_1(esk5_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))|v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.12/0.39  cnf(c_0_69, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.12/0.39  cnf(c_0_70, plain, (r1_tarski(k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_39]), c_0_40]), c_0_41])).
% 0.12/0.39  cnf(c_0_71, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.12/0.39  cnf(c_0_72, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_62]), c_0_39]), c_0_40]), c_0_41])).
% 0.12/0.39  cnf(c_0_73, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.12/0.39  cnf(c_0_74, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.12/0.39  cnf(c_0_75, negated_conjecture, (esk1_1(esk5_0)=esk4_0|v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.12/0.39  cnf(c_0_76, plain, (X1=k1_xboole_0|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_43]), c_0_43]), c_0_27]), c_0_27]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41])).
% 0.12/0.39  cnf(c_0_77, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X1)), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 0.12/0.39  fof(c_0_78, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k5_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.12/0.39  cnf(c_0_79, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73]), c_0_74])).
% 0.12/0.39  cnf(c_0_80, negated_conjecture, (esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.39  fof(c_0_81, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k2_xboole_0(X24,X25)=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.12/0.39  cnf(c_0_82, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.12/0.39  cnf(c_0_83, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_59, c_0_75])).
% 0.12/0.39  cnf(c_0_84, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk5_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_76, c_0_51])).
% 0.12/0.39  cnf(c_0_85, negated_conjecture, (r1_tarski(k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),esk5_0)), inference(spm,[status(thm)],[c_0_77, c_0_47])).
% 0.12/0.39  cnf(c_0_86, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.12/0.39  cnf(c_0_87, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_73]), c_0_79])).
% 0.12/0.39  cnf(c_0_88, negated_conjecture, (esk5_0!=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)|esk6_0!=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_43]), c_0_43]), c_0_27]), c_0_27]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41])).
% 0.12/0.39  cnf(c_0_89, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.12/0.39  cnf(c_0_90, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.12/0.39  cnf(c_0_91, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.12/0.39  cnf(c_0_92, negated_conjecture, (esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.39  cnf(c_0_93, negated_conjecture, (esk5_0=k1_xboole_0|X1=k1_xboole_0|X1=esk5_0|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_76, c_0_84])).
% 0.12/0.39  cnf(c_0_94, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(esk6_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_84]), c_0_86]), c_0_87])).
% 0.12/0.39  cnf(c_0_95, negated_conjecture, (esk5_0=k1_xboole_0|esk6_0!=esk5_0), inference(spm,[status(thm)],[c_0_88, c_0_84])).
% 0.12/0.39  cnf(c_0_96, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.12/0.39  cnf(c_0_97, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.12/0.39  cnf(c_0_98, negated_conjecture, (r1_tarski(esk5_0,X1)|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.12/0.39  cnf(c_0_99, negated_conjecture, (esk5_0!=k1_xboole_0|esk6_0!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.39  cnf(c_0_100, negated_conjecture, (esk6_0!=k1_xboole_0|esk5_0!=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_43]), c_0_27]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.12/0.39  cnf(c_0_101, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95])).
% 0.12/0.39  cnf(c_0_102, plain, (r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_43]), c_0_27]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.12/0.39  cnf(c_0_103, negated_conjecture, (k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1))=X1|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.12/0.39  cnf(c_0_104, negated_conjecture, (esk5_0!=k1_xboole_0|esk6_0!=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_43]), c_0_27]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.12/0.39  cnf(c_0_105, negated_conjecture, (esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_84])).
% 0.12/0.39  cnf(c_0_106, plain, (r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_102])).
% 0.12/0.39  cnf(c_0_107, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk6_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_47, c_0_103])).
% 0.12/0.39  cnf(c_0_108, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_105])])).
% 0.12/0.39  cnf(c_0_109, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_106])).
% 0.12/0.39  cnf(c_0_110, negated_conjecture, (r2_hidden(esk4_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_105]), c_0_108])).
% 0.12/0.39  cnf(c_0_111, negated_conjecture, (r2_hidden(esk4_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 0.12/0.39  cnf(c_0_112, negated_conjecture, (esk4_0=X1), inference(spm,[status(thm)],[c_0_67, c_0_111])).
% 0.12/0.39  cnf(c_0_113, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_112]), c_0_112])]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 114
% 0.12/0.39  # Proof object clause steps            : 69
% 0.12/0.39  # Proof object formula steps           : 45
% 0.12/0.39  # Proof object conjectures             : 32
% 0.12/0.39  # Proof object clause conjectures      : 29
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 28
% 0.12/0.39  # Proof object initial formulas used   : 22
% 0.12/0.39  # Proof object generating inferences   : 20
% 0.12/0.39  # Proof object simplifying inferences  : 115
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 23
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 38
% 0.12/0.39  # Removed in clause preprocessing      : 9
% 0.12/0.39  # Initial clauses in saturation        : 29
% 0.12/0.39  # Processed clauses                    : 364
% 0.12/0.39  # ...of these trivial                  : 27
% 0.12/0.39  # ...subsumed                          : 141
% 0.12/0.39  # ...remaining for further processing  : 196
% 0.12/0.39  # Other redundant clauses eliminated   : 31
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 22
% 0.12/0.39  # Backward-rewritten                   : 134
% 0.12/0.39  # Generated clauses                    : 1876
% 0.12/0.39  # ...of the previous two non-trivial   : 1512
% 0.12/0.39  # Contextual simplify-reflections      : 5
% 0.12/0.39  # Paramodulations                      : 1809
% 0.12/0.39  # Factorizations                       : 38
% 0.12/0.39  # Equation resolutions                 : 31
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 6
% 0.12/0.39  #    Positive orientable unit clauses  : 2
% 0.12/0.39  #    Positive unorientable unit clauses: 1
% 0.12/0.39  #    Negative unit clauses             : 0
% 0.12/0.39  #    Non-unit-clauses                  : 3
% 0.12/0.39  # Current number of unprocessed clauses: 881
% 0.12/0.39  # ...number of literals in the above   : 4219
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 192
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 882
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 447
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 159
% 0.12/0.39  # Unit Clause-clause subsumption calls : 9
% 0.12/0.39  # Rewrite failures with RHS unbound    : 5
% 0.12/0.39  # BW rewrite match attempts            : 119
% 0.12/0.39  # BW rewrite match successes           : 86
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 33868
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.051 s
% 0.12/0.39  # System time              : 0.002 s
% 0.12/0.39  # Total time               : 0.053 s
% 0.12/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
