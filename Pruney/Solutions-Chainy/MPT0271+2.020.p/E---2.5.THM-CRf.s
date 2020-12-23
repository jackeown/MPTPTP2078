%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:47 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 358 expanded)
%              Number of clauses        :   51 ( 149 expanded)
%              Number of leaves         :   20 ( 103 expanded)
%              Depth                    :   10
%              Number of atoms          :  222 ( 736 expanded)
%              Number of equality atoms :   90 ( 413 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

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

fof(t68_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_20,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47,X48,X49,X50] :
      ( ( ~ r2_hidden(X45,X44)
        | X45 = X41
        | X45 = X42
        | X45 = X43
        | X44 != k1_enumset1(X41,X42,X43) )
      & ( X46 != X41
        | r2_hidden(X46,X44)
        | X44 != k1_enumset1(X41,X42,X43) )
      & ( X46 != X42
        | r2_hidden(X46,X44)
        | X44 != k1_enumset1(X41,X42,X43) )
      & ( X46 != X43
        | r2_hidden(X46,X44)
        | X44 != k1_enumset1(X41,X42,X43) )
      & ( esk4_4(X47,X48,X49,X50) != X47
        | ~ r2_hidden(esk4_4(X47,X48,X49,X50),X50)
        | X50 = k1_enumset1(X47,X48,X49) )
      & ( esk4_4(X47,X48,X49,X50) != X48
        | ~ r2_hidden(esk4_4(X47,X48,X49,X50),X50)
        | X50 = k1_enumset1(X47,X48,X49) )
      & ( esk4_4(X47,X48,X49,X50) != X49
        | ~ r2_hidden(esk4_4(X47,X48,X49,X50),X50)
        | X50 = k1_enumset1(X47,X48,X49) )
      & ( r2_hidden(esk4_4(X47,X48,X49,X50),X50)
        | esk4_4(X47,X48,X49,X50) = X47
        | esk4_4(X47,X48,X49,X50) = X48
        | esk4_4(X47,X48,X49,X50) = X49
        | X50 = k1_enumset1(X47,X48,X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_21,plain,(
    ! [X55,X56,X57] : k2_enumset1(X55,X55,X56,X57) = k1_enumset1(X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X58,X59,X60,X61] : k3_enumset1(X58,X58,X59,X60,X61) = k2_enumset1(X58,X59,X60,X61) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_23,plain,(
    ! [X62,X63,X64,X65,X66] : k4_enumset1(X62,X62,X63,X64,X65,X66) = k3_enumset1(X62,X63,X64,X65,X66) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_24,plain,(
    ! [X67,X68,X69,X70,X71,X72] : k5_enumset1(X67,X67,X68,X69,X70,X71,X72) = k4_enumset1(X67,X68,X69,X70,X71,X72) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
      <=> r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t68_zfmisc_1])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,negated_conjecture,
    ( ( k4_xboole_0(k1_tarski(esk5_0),esk6_0) != k1_xboole_0
      | ~ r2_hidden(esk5_0,esk6_0) )
    & ( k4_xboole_0(k1_tarski(esk5_0),esk6_0) = k1_xboole_0
      | r2_hidden(esk5_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_32,plain,(
    ! [X52] : k2_tarski(X52,X52) = k1_tarski(X52) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_33,plain,(
    ! [X53,X54] : k1_enumset1(X53,X53,X54) = k2_tarski(X53,X54) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_34,plain,(
    ! [X33,X34] : k4_xboole_0(X33,X34) = k5_xboole_0(X33,k3_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_35,plain,(
    ! [X27,X28,X30,X31,X32] :
      ( ( r1_xboole_0(X27,X28)
        | r2_hidden(esk3_2(X27,X28),k3_xboole_0(X27,X28)) )
      & ( ~ r2_hidden(X32,k3_xboole_0(X30,X31))
        | ~ r1_xboole_0(X30,X31) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_36,plain,(
    ! [X40] : r1_xboole_0(X40,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_37,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( r2_hidden(X18,X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X15)
        | ~ r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk2_3(X20,X21,X22),X22)
        | ~ r2_hidden(esk2_3(X20,X21,X22),X20)
        | ~ r2_hidden(esk2_3(X20,X21,X22),X21)
        | X22 = k3_xboole_0(X20,X21) )
      & ( r2_hidden(esk2_3(X20,X21,X22),X20)
        | r2_hidden(esk2_3(X20,X21,X22),X22)
        | X22 = k3_xboole_0(X20,X21) )
      & ( r2_hidden(esk2_3(X20,X21,X22),X21)
        | r2_hidden(esk2_3(X20,X21,X22),X22)
        | X22 = k3_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_39,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r2_hidden(X24,X25)
        | ~ r2_hidden(X24,X26)
        | ~ r2_hidden(X24,k5_xboole_0(X25,X26)) )
      & ( r2_hidden(X24,X25)
        | r2_hidden(X24,X26)
        | ~ r2_hidden(X24,k5_xboole_0(X25,X26)) )
      & ( ~ r2_hidden(X24,X25)
        | r2_hidden(X24,X26)
        | r2_hidden(X24,k5_xboole_0(X25,X26)) )
      & ( ~ r2_hidden(X24,X26)
        | r2_hidden(X24,X25)
        | r2_hidden(X24,k5_xboole_0(X25,X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk5_0),esk6_0) = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_45,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_48,plain,(
    ! [X36] : k3_xboole_0(X36,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X4,X4,X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_27]),c_0_28]),c_0_29]),c_0_30])).

fof(c_0_51,plain,(
    ! [X75,X76] : k3_tarski(k2_tarski(X75,X76)) = k2_xboole_0(X75,X76) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).

cnf(c_0_54,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)) = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).

fof(c_0_60,plain,(
    ! [X37,X38,X39] :
      ( ~ r1_tarski(X37,k2_xboole_0(X38,X39))
      | r1_tarski(k4_xboole_0(X37,X38),X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_61,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_62,plain,(
    ! [X35] : k2_xboole_0(X35,k1_xboole_0) = X35 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_63,plain,(
    ! [X73,X74] :
      ( ( ~ r1_tarski(k1_tarski(X73),X74)
        | r2_hidden(X73,X74) )
      & ( ~ r2_hidden(X73,X74)
        | r1_tarski(k1_tarski(X73),X74) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k5_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X3,X1),X4))
    | r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X1,X4)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_61,c_0_43])).

cnf(c_0_71,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk5_0,k3_xboole_0(esk6_0,k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk5_0),esk6_0) != k1_xboole_0
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_76,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_77,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_78,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_44]),c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_79,plain,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_70]),c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_80,plain,
    ( r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_42]),c_0_43]),c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)) != k1_xboole_0
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_42]),c_0_43]),c_0_44]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30])).

cnf(c_0_83,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_84,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(X2,k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_77]),c_0_57])).

cnf(c_0_85,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) != k1_xboole_0
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_55])).

cnf(c_0_88,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(X2,k1_xboole_0,X1),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_55])).

cnf(c_0_90,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_81])])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.67/1.85  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 1.67/1.85  # and selection function GSelectMinInfpos.
% 1.67/1.85  #
% 1.67/1.85  # Preprocessing time       : 0.028 s
% 1.67/1.85  # Presaturation interreduction done
% 1.67/1.85  
% 1.67/1.85  # Proof found!
% 1.67/1.85  # SZS status Theorem
% 1.67/1.85  # SZS output start CNFRefutation
% 1.67/1.85  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.67/1.85  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.67/1.85  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.67/1.85  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.67/1.85  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.67/1.85  fof(t68_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 1.67/1.85  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.67/1.85  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.67/1.85  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.67/1.85  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.67/1.85  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.67/1.85  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.67/1.85  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 1.67/1.85  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.67/1.85  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.67/1.85  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.67/1.85  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.67/1.85  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.67/1.85  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.67/1.85  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.67/1.85  fof(c_0_20, plain, ![X41, X42, X43, X44, X45, X46, X47, X48, X49, X50]:(((~r2_hidden(X45,X44)|(X45=X41|X45=X42|X45=X43)|X44!=k1_enumset1(X41,X42,X43))&(((X46!=X41|r2_hidden(X46,X44)|X44!=k1_enumset1(X41,X42,X43))&(X46!=X42|r2_hidden(X46,X44)|X44!=k1_enumset1(X41,X42,X43)))&(X46!=X43|r2_hidden(X46,X44)|X44!=k1_enumset1(X41,X42,X43))))&((((esk4_4(X47,X48,X49,X50)!=X47|~r2_hidden(esk4_4(X47,X48,X49,X50),X50)|X50=k1_enumset1(X47,X48,X49))&(esk4_4(X47,X48,X49,X50)!=X48|~r2_hidden(esk4_4(X47,X48,X49,X50),X50)|X50=k1_enumset1(X47,X48,X49)))&(esk4_4(X47,X48,X49,X50)!=X49|~r2_hidden(esk4_4(X47,X48,X49,X50),X50)|X50=k1_enumset1(X47,X48,X49)))&(r2_hidden(esk4_4(X47,X48,X49,X50),X50)|(esk4_4(X47,X48,X49,X50)=X47|esk4_4(X47,X48,X49,X50)=X48|esk4_4(X47,X48,X49,X50)=X49)|X50=k1_enumset1(X47,X48,X49)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 1.67/1.86  fof(c_0_21, plain, ![X55, X56, X57]:k2_enumset1(X55,X55,X56,X57)=k1_enumset1(X55,X56,X57), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.67/1.86  fof(c_0_22, plain, ![X58, X59, X60, X61]:k3_enumset1(X58,X58,X59,X60,X61)=k2_enumset1(X58,X59,X60,X61), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.67/1.86  fof(c_0_23, plain, ![X62, X63, X64, X65, X66]:k4_enumset1(X62,X62,X63,X64,X65,X66)=k3_enumset1(X62,X63,X64,X65,X66), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 1.67/1.86  fof(c_0_24, plain, ![X67, X68, X69, X70, X71, X72]:k5_enumset1(X67,X67,X68,X69,X70,X71,X72)=k4_enumset1(X67,X68,X69,X70,X71,X72), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 1.67/1.86  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2))), inference(assume_negation,[status(cth)],[t68_zfmisc_1])).
% 1.67/1.86  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.67/1.86  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.67/1.86  cnf(c_0_28, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.67/1.86  cnf(c_0_29, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.67/1.86  cnf(c_0_30, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.67/1.86  fof(c_0_31, negated_conjecture, ((k4_xboole_0(k1_tarski(esk5_0),esk6_0)!=k1_xboole_0|~r2_hidden(esk5_0,esk6_0))&(k4_xboole_0(k1_tarski(esk5_0),esk6_0)=k1_xboole_0|r2_hidden(esk5_0,esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 1.67/1.86  fof(c_0_32, plain, ![X52]:k2_tarski(X52,X52)=k1_tarski(X52), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.67/1.86  fof(c_0_33, plain, ![X53, X54]:k1_enumset1(X53,X53,X54)=k2_tarski(X53,X54), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.67/1.86  fof(c_0_34, plain, ![X33, X34]:k4_xboole_0(X33,X34)=k5_xboole_0(X33,k3_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.67/1.86  fof(c_0_35, plain, ![X27, X28, X30, X31, X32]:((r1_xboole_0(X27,X28)|r2_hidden(esk3_2(X27,X28),k3_xboole_0(X27,X28)))&(~r2_hidden(X32,k3_xboole_0(X30,X31))|~r1_xboole_0(X30,X31))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 1.67/1.86  fof(c_0_36, plain, ![X40]:r1_xboole_0(X40,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 1.67/1.86  fof(c_0_37, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:((((r2_hidden(X18,X15)|~r2_hidden(X18,X17)|X17!=k3_xboole_0(X15,X16))&(r2_hidden(X18,X16)|~r2_hidden(X18,X17)|X17!=k3_xboole_0(X15,X16)))&(~r2_hidden(X19,X15)|~r2_hidden(X19,X16)|r2_hidden(X19,X17)|X17!=k3_xboole_0(X15,X16)))&((~r2_hidden(esk2_3(X20,X21,X22),X22)|(~r2_hidden(esk2_3(X20,X21,X22),X20)|~r2_hidden(esk2_3(X20,X21,X22),X21))|X22=k3_xboole_0(X20,X21))&((r2_hidden(esk2_3(X20,X21,X22),X20)|r2_hidden(esk2_3(X20,X21,X22),X22)|X22=k3_xboole_0(X20,X21))&(r2_hidden(esk2_3(X20,X21,X22),X21)|r2_hidden(esk2_3(X20,X21,X22),X22)|X22=k3_xboole_0(X20,X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 1.67/1.86  cnf(c_0_38, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.67/1.86  fof(c_0_39, plain, ![X24, X25, X26]:(((~r2_hidden(X24,X25)|~r2_hidden(X24,X26)|~r2_hidden(X24,k5_xboole_0(X25,X26)))&(r2_hidden(X24,X25)|r2_hidden(X24,X26)|~r2_hidden(X24,k5_xboole_0(X25,X26))))&((~r2_hidden(X24,X25)|r2_hidden(X24,X26)|r2_hidden(X24,k5_xboole_0(X25,X26)))&(~r2_hidden(X24,X26)|r2_hidden(X24,X25)|r2_hidden(X24,k5_xboole_0(X25,X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 1.67/1.86  cnf(c_0_40, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 1.67/1.86  cnf(c_0_41, negated_conjecture, (k4_xboole_0(k1_tarski(esk5_0),esk6_0)=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.67/1.86  cnf(c_0_42, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.67/1.86  cnf(c_0_43, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.67/1.86  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.67/1.86  fof(c_0_45, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.67/1.86  cnf(c_0_46, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.67/1.86  cnf(c_0_47, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.67/1.86  fof(c_0_48, plain, ![X36]:k3_xboole_0(X36,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 1.67/1.86  cnf(c_0_49, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.67/1.86  cnf(c_0_50, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X4,X4,X4,X4,X2,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 1.67/1.86  fof(c_0_51, plain, ![X75, X76]:k3_tarski(k2_tarski(X75,X76))=k2_xboole_0(X75,X76), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.67/1.86  cnf(c_0_52, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.67/1.86  cnf(c_0_53, plain, (r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).
% 1.67/1.86  cnf(c_0_54, negated_conjecture, (k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0))=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30])).
% 1.67/1.86  cnf(c_0_55, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.67/1.86  cnf(c_0_56, plain, (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.67/1.86  cnf(c_0_57, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.67/1.86  cnf(c_0_58, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_49])).
% 1.67/1.86  cnf(c_0_59, plain, (r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X1,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).
% 1.67/1.86  fof(c_0_60, plain, ![X37, X38, X39]:(~r1_tarski(X37,k2_xboole_0(X38,X39))|r1_tarski(k4_xboole_0(X37,X38),X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 1.67/1.86  cnf(c_0_61, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.67/1.86  fof(c_0_62, plain, ![X35]:k2_xboole_0(X35,k1_xboole_0)=X35, inference(variable_rename,[status(thm)],[t1_boole])).
% 1.67/1.86  fof(c_0_63, plain, ![X73, X74]:((~r1_tarski(k1_tarski(X73),X74)|r2_hidden(X73,X74))&(~r2_hidden(X73,X74)|r1_tarski(k1_tarski(X73),X74))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 1.67/1.86  cnf(c_0_64, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.67/1.86  cnf(c_0_65, plain, (r2_hidden(X1,k5_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X3,X1),X4))|r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.67/1.86  cnf(c_0_66, negated_conjecture, (k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 1.67/1.86  cnf(c_0_67, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 1.67/1.86  cnf(c_0_68, plain, (r2_hidden(X1,k3_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X1,X4)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 1.67/1.86  cnf(c_0_69, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 1.67/1.86  cnf(c_0_70, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_61, c_0_43])).
% 1.67/1.86  cnf(c_0_71, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.67/1.86  cnf(c_0_72, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 1.67/1.86  cnf(c_0_73, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_64])).
% 1.67/1.86  cnf(c_0_74, negated_conjecture, (r2_hidden(esk5_0,k3_xboole_0(esk6_0,k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_68])).
% 1.67/1.86  cnf(c_0_75, negated_conjecture, (k4_xboole_0(k1_tarski(esk5_0),esk6_0)!=k1_xboole_0|~r2_hidden(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.67/1.86  fof(c_0_76, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk1_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk1_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.67/1.86  cnf(c_0_77, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.67/1.86  cnf(c_0_78, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_44]), c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 1.67/1.86  cnf(c_0_79, plain, (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_70]), c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 1.67/1.86  cnf(c_0_80, plain, (r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_42]), c_0_43]), c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 1.67/1.86  cnf(c_0_81, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 1.67/1.86  cnf(c_0_82, negated_conjecture, (k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0))!=k1_xboole_0|~r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_42]), c_0_43]), c_0_44]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30])).
% 1.67/1.86  cnf(c_0_83, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 1.67/1.86  cnf(c_0_84, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(X2,k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_77]), c_0_57])).
% 1.67/1.86  cnf(c_0_85, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 1.67/1.86  cnf(c_0_86, negated_conjecture, (r1_tarski(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 1.67/1.86  cnf(c_0_87, negated_conjecture, (k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))!=k1_xboole_0|~r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_82, c_0_55])).
% 1.67/1.86  cnf(c_0_88, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(X2,k1_xboole_0,X1),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 1.67/1.86  cnf(c_0_89, negated_conjecture, (r1_tarski(k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_55])).
% 1.67/1.86  cnf(c_0_90, negated_conjecture, (k5_xboole_0(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_81])])).
% 1.67/1.86  cnf(c_0_91, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90]), c_0_67]), ['proof']).
% 1.67/1.86  # SZS output end CNFRefutation
% 1.67/1.86  # Proof object total steps             : 92
% 1.67/1.86  # Proof object clause steps            : 51
% 1.67/1.86  # Proof object formula steps           : 41
% 1.67/1.86  # Proof object conjectures             : 15
% 1.67/1.86  # Proof object clause conjectures      : 12
% 1.67/1.86  # Proof object formula conjectures     : 3
% 1.67/1.86  # Proof object initial clauses used    : 24
% 1.67/1.86  # Proof object initial formulas used   : 20
% 1.67/1.86  # Proof object generating inferences   : 11
% 1.67/1.86  # Proof object simplifying inferences  : 65
% 1.67/1.86  # Training examples: 0 positive, 0 negative
% 1.67/1.86  # Parsed axioms                        : 20
% 1.67/1.86  # Removed by relevancy pruning/SinE    : 0
% 1.67/1.86  # Initial clauses                      : 40
% 1.67/1.86  # Removed in clause preprocessing      : 8
% 1.67/1.86  # Initial clauses in saturation        : 32
% 1.67/1.86  # Processed clauses                    : 4853
% 1.67/1.86  # ...of these trivial                  : 195
% 1.67/1.86  # ...subsumed                          : 3401
% 1.67/1.86  # ...remaining for further processing  : 1257
% 1.67/1.86  # Other redundant clauses eliminated   : 168
% 1.67/1.86  # Clauses deleted for lack of memory   : 0
% 1.67/1.86  # Backward-subsumed                    : 15
% 1.67/1.86  # Backward-rewritten                   : 594
% 1.67/1.86  # Generated clauses                    : 80767
% 1.67/1.86  # ...of the previous two non-trivial   : 69036
% 1.67/1.86  # Contextual simplify-reflections      : 3
% 1.67/1.86  # Paramodulations                      : 80381
% 1.67/1.86  # Factorizations                       : 221
% 1.67/1.86  # Equation resolutions                 : 168
% 1.67/1.86  # Propositional unsat checks           : 0
% 1.67/1.86  #    Propositional check models        : 0
% 1.67/1.86  #    Propositional check unsatisfiable : 0
% 1.67/1.86  #    Propositional clauses             : 0
% 1.67/1.86  #    Propositional clauses after purity: 0
% 1.67/1.86  #    Propositional unsat core size     : 0
% 1.67/1.86  #    Propositional preprocessing time  : 0.000
% 1.67/1.86  #    Propositional encoding time       : 0.000
% 1.67/1.86  #    Propositional solver time         : 0.000
% 1.67/1.86  #    Success case prop preproc time    : 0.000
% 1.67/1.86  #    Success case prop encoding time   : 0.000
% 1.67/1.86  #    Success case prop solver time     : 0.000
% 1.67/1.86  # Current number of processed clauses  : 609
% 1.67/1.86  #    Positive orientable unit clauses  : 67
% 1.67/1.86  #    Positive unorientable unit clauses: 1
% 1.67/1.86  #    Negative unit clauses             : 21
% 1.67/1.86  #    Non-unit-clauses                  : 520
% 1.67/1.86  # Current number of unprocessed clauses: 61422
% 1.67/1.86  # ...number of literals in the above   : 424748
% 1.67/1.86  # Current number of archived formulas  : 0
% 1.67/1.86  # Current number of archived clauses   : 649
% 1.67/1.86  # Clause-clause subsumption calls (NU) : 53001
% 1.67/1.86  # Rec. Clause-clause subsumption calls : 34167
% 1.67/1.86  # Non-unit clause-clause subsumptions  : 1443
% 1.67/1.86  # Unit Clause-clause subsumption calls : 12417
% 1.67/1.86  # Rewrite failures with RHS unbound    : 0
% 1.67/1.86  # BW rewrite match attempts            : 1165
% 1.67/1.86  # BW rewrite match successes           : 75
% 1.67/1.86  # Condensation attempts                : 0
% 1.67/1.86  # Condensation successes               : 0
% 1.67/1.86  # Termbank termtop insertions          : 1896302
% 1.67/1.86  
% 1.67/1.86  # -------------------------------------------------
% 1.67/1.86  # User time                : 1.471 s
% 1.67/1.86  # System time              : 0.046 s
% 1.67/1.86  # Total time               : 1.517 s
% 1.67/1.86  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
