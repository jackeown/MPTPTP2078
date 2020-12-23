%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:51 EST 2020

% Result     : Theorem 0.52s
% Output     : CNFRefutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  111 (3475 expanded)
%              Number of clauses        :   72 (1464 expanded)
%              Number of leaves         :   19 ( 974 expanded)
%              Depth                    :   15
%              Number of atoms          :  258 (6127 expanded)
%              Number of equality atoms :  138 (4810 expanded)
%              Maximal formula depth    :   17 (   3 average)
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

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

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

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_19,plain,(
    ! [X60,X61] : k3_tarski(k2_tarski(X60,X61)) = k2_xboole_0(X60,X61) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X53,X54] : k1_enumset1(X53,X53,X54) = k2_tarski(X53,X54) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X40,X41] : k4_xboole_0(X40,k2_xboole_0(X40,X41)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_23,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X32,X33] : k4_xboole_0(X32,X33) = k5_xboole_0(X32,k3_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_26,plain,(
    ! [X55,X56,X57] : k2_enumset1(X55,X55,X56,X57) = k1_enumset1(X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,negated_conjecture,
    ( k1_tarski(esk6_0) = k2_xboole_0(esk7_0,esk8_0)
    & ( esk7_0 != k1_tarski(esk6_0)
      | esk8_0 != k1_tarski(esk6_0) )
    & ( esk7_0 != k1_xboole_0
      | esk8_0 != k1_tarski(esk6_0) )
    & ( esk7_0 != k1_tarski(esk6_0)
      | esk8_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_28,plain,(
    ! [X52] : k2_tarski(X52,X52) = k1_tarski(X52) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_29,plain,(
    ! [X42,X43] : k4_xboole_0(X42,k4_xboole_0(X42,X43)) = k3_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k1_tarski(esk6_0) = k2_xboole_0(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) = k3_tarski(k2_enumset1(esk7_0,esk7_0,esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_24]),c_0_31]),c_0_33]),c_0_33])).

fof(c_0_39,plain,(
    ! [X39] : k3_xboole_0(X39,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_40,plain,(
    ! [X44] : k5_xboole_0(X44,k1_xboole_0) = X44 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_41,plain,(
    ! [X20,X21] :
      ( ( ~ r1_xboole_0(X20,X21)
        | k3_xboole_0(X20,X21) = k1_xboole_0 )
      & ( k3_xboole_0(X20,X21) != k1_xboole_0
        | r1_xboole_0(X20,X21) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_42,plain,(
    ! [X22,X23,X25,X26,X27] :
      ( ( r2_hidden(esk3_2(X22,X23),X22)
        | r1_xboole_0(X22,X23) )
      & ( r2_hidden(esk3_2(X22,X23),X23)
        | r1_xboole_0(X22,X23) )
      & ( ~ r2_hidden(X27,X25)
        | ~ r2_hidden(X27,X26)
        | ~ r1_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_43,plain,(
    ! [X45,X46,X47,X48,X49,X50] :
      ( ( ~ r2_hidden(X47,X46)
        | X47 = X45
        | X46 != k1_tarski(X45) )
      & ( X48 != X45
        | r2_hidden(X48,X46)
        | X46 != k1_tarski(X45) )
      & ( ~ r2_hidden(esk5_2(X49,X50),X50)
        | esk5_2(X49,X50) != X49
        | X50 = k1_tarski(X49) )
      & ( r2_hidden(esk5_2(X49,X50),X50)
        | esk5_2(X49,X50) = X49
        | X50 = k1_tarski(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_44,plain,(
    ! [X34,X35,X36] :
      ( ~ r1_tarski(X34,X35)
      | r1_tarski(X34,k2_xboole_0(X36,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_45,plain,(
    ! [X30,X31] :
      ( ( r1_tarski(X30,X31)
        | X30 != X31 )
      & ( r1_tarski(X31,X30)
        | X30 != X31 )
      & ( ~ r1_tarski(X30,X31)
        | ~ r1_tarski(X31,X30)
        | X30 = X31 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_32]),c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_52,plain,(
    ! [X37,X38] :
      ( ~ r1_tarski(X37,X38)
      | k2_xboole_0(X37,X38) = X38 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,negated_conjecture,
    ( k3_xboole_0(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) = esk7_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk3_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_61,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_48])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_35]),c_0_24]),c_0_33])).

fof(c_0_65,plain,(
    ! [X58,X59] :
      ( ( ~ r1_tarski(X58,k1_tarski(X59))
        | X58 = k1_xboole_0
        | X58 = k1_tarski(X59) )
      & ( X58 != k1_xboole_0
        | r1_tarski(X58,k1_tarski(X59)) )
      & ( X58 != k1_tarski(X59)
        | r1_tarski(X58,k1_tarski(X59)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,k3_tarski(k2_enumset1(X3,X3,X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_31]),c_0_33])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_56])).

fof(c_0_68,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk3_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_57])).

cnf(c_0_70,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_71,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_31]),c_0_33])).

cnf(c_0_72,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_64])])).

cnf(c_0_75,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( esk7_0 != k1_tarski(esk6_0)
    | esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_78,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( esk7_0 != k1_tarski(esk6_0)
    | esk8_0 != k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_80,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_69])).

cnf(c_0_81,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_82,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | esk8_0 != k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_83,negated_conjecture,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,esk8_0)) = k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)
    | r2_hidden(esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_70])).

cnf(c_0_84,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = X2
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_86,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_35]),c_0_35]),c_0_24]),c_0_24]),c_0_33]),c_0_33])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk8_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_38])).

cnf(c_0_88,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    | esk7_0 != k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_35]),c_0_24]),c_0_33])).

cnf(c_0_89,negated_conjecture,
    ( X1 = esk7_0
    | r2_hidden(esk2_3(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),X1),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))
    | r2_hidden(esk2_3(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_78])).

cnf(c_0_90,negated_conjecture,
    ( esk7_0 != k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)
    | esk8_0 != k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_35]),c_0_35]),c_0_24]),c_0_24]),c_0_33]),c_0_33])).

cnf(c_0_91,negated_conjecture,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,esk8_0)) = k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)
    | r2_hidden(esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_80])).

cnf(c_0_92,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_35]),c_0_24]),c_0_33])).

cnf(c_0_93,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | esk8_0 != k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_35]),c_0_24]),c_0_33])).

cnf(c_0_94,negated_conjecture,
    ( k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) = esk8_0
    | r2_hidden(esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_95,negated_conjecture,
    ( k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) = esk8_0
    | esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))
    | esk8_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))
    | esk8_0 != esk7_0 ),
    inference(spm,[status(thm)],[c_0_90,c_0_89])).

cnf(c_0_98,negated_conjecture,
    ( k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) = esk8_0
    | r2_hidden(esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_84]),c_0_85])).

cnf(c_0_99,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_92])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_70])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_89]),c_0_96]),c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_98]),c_0_80])).

cnf(c_0_103,negated_conjecture,
    ( esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_104,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_105,negated_conjecture,
    ( esk2_3(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_99,c_0_101])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_58]),c_0_74]),c_0_106])])).

cnf(c_0_108,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_107])])).

cnf(c_0_109,negated_conjecture,
    ( esk8_0 != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_107]),c_0_107])])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_95,c_0_108]),c_0_107]),c_0_109]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:04:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.52/0.70  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.52/0.70  # and selection function SelectNegativeLiterals.
% 0.52/0.70  #
% 0.52/0.70  # Preprocessing time       : 0.029 s
% 0.52/0.70  # Presaturation interreduction done
% 0.52/0.70  
% 0.52/0.70  # Proof found!
% 0.52/0.70  # SZS status Theorem
% 0.52/0.70  # SZS output start CNFRefutation
% 0.52/0.70  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.52/0.70  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.52/0.70  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.52/0.70  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.52/0.70  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.52/0.70  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.52/0.70  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.52/0.70  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.52/0.70  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.52/0.70  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.52/0.70  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.52/0.70  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.52/0.70  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.52/0.70  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.52/0.70  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.52/0.70  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.52/0.70  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.52/0.70  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.52/0.70  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.52/0.70  fof(c_0_19, plain, ![X60, X61]:k3_tarski(k2_tarski(X60,X61))=k2_xboole_0(X60,X61), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.52/0.70  fof(c_0_20, plain, ![X53, X54]:k1_enumset1(X53,X53,X54)=k2_tarski(X53,X54), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.52/0.70  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.52/0.70  fof(c_0_22, plain, ![X40, X41]:k4_xboole_0(X40,k2_xboole_0(X40,X41))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.52/0.70  cnf(c_0_23, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.52/0.70  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.52/0.70  fof(c_0_25, plain, ![X32, X33]:k4_xboole_0(X32,X33)=k5_xboole_0(X32,k3_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.52/0.70  fof(c_0_26, plain, ![X55, X56, X57]:k2_enumset1(X55,X55,X56,X57)=k1_enumset1(X55,X56,X57), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.52/0.70  fof(c_0_27, negated_conjecture, (((k1_tarski(esk6_0)=k2_xboole_0(esk7_0,esk8_0)&(esk7_0!=k1_tarski(esk6_0)|esk8_0!=k1_tarski(esk6_0)))&(esk7_0!=k1_xboole_0|esk8_0!=k1_tarski(esk6_0)))&(esk7_0!=k1_tarski(esk6_0)|esk8_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.52/0.70  fof(c_0_28, plain, ![X52]:k2_tarski(X52,X52)=k1_tarski(X52), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.52/0.70  fof(c_0_29, plain, ![X42, X43]:k4_xboole_0(X42,k4_xboole_0(X42,X43))=k3_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.52/0.70  cnf(c_0_30, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.52/0.70  cnf(c_0_31, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.52/0.70  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.52/0.70  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.52/0.70  cnf(c_0_34, negated_conjecture, (k1_tarski(esk6_0)=k2_xboole_0(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.52/0.70  cnf(c_0_35, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.52/0.70  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.52/0.70  cnf(c_0_37, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])).
% 0.52/0.70  cnf(c_0_38, negated_conjecture, (k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)=k3_tarski(k2_enumset1(esk7_0,esk7_0,esk7_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_24]), c_0_31]), c_0_33]), c_0_33])).
% 0.52/0.70  fof(c_0_39, plain, ![X39]:k3_xboole_0(X39,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.52/0.70  fof(c_0_40, plain, ![X44]:k5_xboole_0(X44,k1_xboole_0)=X44, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.52/0.70  fof(c_0_41, plain, ![X20, X21]:((~r1_xboole_0(X20,X21)|k3_xboole_0(X20,X21)=k1_xboole_0)&(k3_xboole_0(X20,X21)!=k1_xboole_0|r1_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.52/0.70  fof(c_0_42, plain, ![X22, X23, X25, X26, X27]:(((r2_hidden(esk3_2(X22,X23),X22)|r1_xboole_0(X22,X23))&(r2_hidden(esk3_2(X22,X23),X23)|r1_xboole_0(X22,X23)))&(~r2_hidden(X27,X25)|~r2_hidden(X27,X26)|~r1_xboole_0(X25,X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.52/0.70  fof(c_0_43, plain, ![X45, X46, X47, X48, X49, X50]:(((~r2_hidden(X47,X46)|X47=X45|X46!=k1_tarski(X45))&(X48!=X45|r2_hidden(X48,X46)|X46!=k1_tarski(X45)))&((~r2_hidden(esk5_2(X49,X50),X50)|esk5_2(X49,X50)!=X49|X50=k1_tarski(X49))&(r2_hidden(esk5_2(X49,X50),X50)|esk5_2(X49,X50)=X49|X50=k1_tarski(X49)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.52/0.70  fof(c_0_44, plain, ![X34, X35, X36]:(~r1_tarski(X34,X35)|r1_tarski(X34,k2_xboole_0(X36,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.52/0.70  fof(c_0_45, plain, ![X30, X31]:(((r1_tarski(X30,X31)|X30!=X31)&(r1_tarski(X31,X30)|X30!=X31))&(~r1_tarski(X30,X31)|~r1_tarski(X31,X30)|X30=X31)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.52/0.70  cnf(c_0_46, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_32]), c_0_32])).
% 0.52/0.70  cnf(c_0_47, negated_conjecture, (k5_xboole_0(esk7_0,k3_xboole_0(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.52/0.70  cnf(c_0_48, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.52/0.70  cnf(c_0_49, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.52/0.70  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.52/0.70  cnf(c_0_51, plain, (r2_hidden(esk3_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.52/0.70  fof(c_0_52, plain, ![X37, X38]:(~r1_tarski(X37,X38)|k2_xboole_0(X37,X38)=X38), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.52/0.70  cnf(c_0_53, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.52/0.70  cnf(c_0_54, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.52/0.70  cnf(c_0_55, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.52/0.70  cnf(c_0_56, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.52/0.70  cnf(c_0_57, plain, (r2_hidden(esk3_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.52/0.70  cnf(c_0_58, negated_conjecture, (k3_xboole_0(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))=esk7_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49])).
% 0.52/0.70  cnf(c_0_59, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk3_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.52/0.70  cnf(c_0_60, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.52/0.70  fof(c_0_61, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.52/0.70  cnf(c_0_62, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.52/0.70  cnf(c_0_63, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_48])).
% 0.52/0.70  cnf(c_0_64, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_35]), c_0_24]), c_0_33])).
% 0.52/0.70  fof(c_0_65, plain, ![X58, X59]:((~r1_tarski(X58,k1_tarski(X59))|(X58=k1_xboole_0|X58=k1_tarski(X59)))&((X58!=k1_xboole_0|r1_tarski(X58,k1_tarski(X59)))&(X58!=k1_tarski(X59)|r1_tarski(X58,k1_tarski(X59))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.52/0.70  cnf(c_0_66, plain, (r1_tarski(X1,k3_tarski(k2_enumset1(X3,X3,X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_31]), c_0_33])).
% 0.52/0.70  cnf(c_0_67, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_56])).
% 0.52/0.70  fof(c_0_68, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.52/0.70  cnf(c_0_69, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk3_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_50, c_0_57])).
% 0.52/0.70  cnf(c_0_70, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.52/0.70  cnf(c_0_71, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_31]), c_0_33])).
% 0.52/0.70  cnf(c_0_72, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.52/0.70  cnf(c_0_73, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.52/0.70  cnf(c_0_74, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_64])])).
% 0.52/0.70  cnf(c_0_75, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.52/0.70  cnf(c_0_76, plain, (r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.52/0.70  cnf(c_0_77, negated_conjecture, (esk7_0!=k1_tarski(esk6_0)|esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.52/0.70  cnf(c_0_78, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.52/0.70  cnf(c_0_79, negated_conjecture, (esk7_0!=k1_tarski(esk6_0)|esk8_0!=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.52/0.70  cnf(c_0_80, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),esk7_0)), inference(spm,[status(thm)],[c_0_58, c_0_69])).
% 0.52/0.70  cnf(c_0_81, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.52/0.70  cnf(c_0_82, negated_conjecture, (esk7_0!=k1_xboole_0|esk8_0!=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.52/0.70  cnf(c_0_83, negated_conjecture, (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,esk8_0))=k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)|r2_hidden(esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_38, c_0_70])).
% 0.52/0.70  cnf(c_0_84, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X2))=X2|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.52/0.70  cnf(c_0_85, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.52/0.70  cnf(c_0_86, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_35]), c_0_35]), c_0_24]), c_0_24]), c_0_33]), c_0_33])).
% 0.52/0.70  cnf(c_0_87, negated_conjecture, (r1_tarski(esk8_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_76, c_0_38])).
% 0.52/0.70  cnf(c_0_88, negated_conjecture, (esk8_0!=k1_xboole_0|esk7_0!=k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_35]), c_0_24]), c_0_33])).
% 0.52/0.70  cnf(c_0_89, negated_conjecture, (X1=esk7_0|r2_hidden(esk2_3(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),X1),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))|r2_hidden(esk2_3(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),X1),X1)), inference(spm,[status(thm)],[c_0_58, c_0_78])).
% 0.52/0.70  cnf(c_0_90, negated_conjecture, (esk7_0!=k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)|esk8_0!=k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_35]), c_0_35]), c_0_24]), c_0_24]), c_0_33]), c_0_33])).
% 0.52/0.70  cnf(c_0_91, negated_conjecture, (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,esk8_0))=k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)|r2_hidden(esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),esk7_0)), inference(spm,[status(thm)],[c_0_38, c_0_80])).
% 0.52/0.70  cnf(c_0_92, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_35]), c_0_24]), c_0_33])).
% 0.52/0.70  cnf(c_0_93, negated_conjecture, (esk7_0!=k1_xboole_0|esk8_0!=k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_35]), c_0_24]), c_0_33])).
% 0.52/0.70  cnf(c_0_94, negated_conjecture, (k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)=esk8_0|r2_hidden(esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 0.52/0.70  cnf(c_0_95, negated_conjecture, (k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)=esk8_0|esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.52/0.70  cnf(c_0_96, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))|esk8_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.52/0.70  cnf(c_0_97, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))|esk8_0!=esk7_0), inference(spm,[status(thm)],[c_0_90, c_0_89])).
% 0.52/0.70  cnf(c_0_98, negated_conjecture, (k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)=esk8_0|r2_hidden(esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_84]), c_0_85])).
% 0.52/0.70  cnf(c_0_99, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_92])).
% 0.52/0.70  cnf(c_0_100, negated_conjecture, (r2_hidden(esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_70])).
% 0.52/0.70  cnf(c_0_101, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_89]), c_0_96]), c_0_97])).
% 0.52/0.70  cnf(c_0_102, negated_conjecture, (r2_hidden(esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_98]), c_0_80])).
% 0.52/0.70  cnf(c_0_103, negated_conjecture, (esk3_2(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))=esk6_0), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.52/0.70  cnf(c_0_104, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.52/0.70  cnf(c_0_105, negated_conjecture, (esk2_3(esk7_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))=esk6_0), inference(spm,[status(thm)],[c_0_99, c_0_101])).
% 0.52/0.70  cnf(c_0_106, negated_conjecture, (r2_hidden(esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_102, c_0_103])).
% 0.52/0.70  cnf(c_0_107, negated_conjecture, (k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_58]), c_0_74]), c_0_106])])).
% 0.52/0.70  cnf(c_0_108, negated_conjecture, (esk8_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_107])])).
% 0.52/0.70  cnf(c_0_109, negated_conjecture, (esk8_0!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_107]), c_0_107])])).
% 0.52/0.70  cnf(c_0_110, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_95, c_0_108]), c_0_107]), c_0_109]), ['proof']).
% 0.52/0.70  # SZS output end CNFRefutation
% 0.52/0.70  # Proof object total steps             : 111
% 0.52/0.70  # Proof object clause steps            : 72
% 0.52/0.70  # Proof object formula steps           : 39
% 0.52/0.70  # Proof object conjectures             : 34
% 0.52/0.70  # Proof object clause conjectures      : 31
% 0.52/0.70  # Proof object formula conjectures     : 3
% 0.52/0.70  # Proof object initial clauses used    : 27
% 0.52/0.70  # Proof object initial formulas used   : 19
% 0.52/0.70  # Proof object generating inferences   : 26
% 0.52/0.70  # Proof object simplifying inferences  : 64
% 0.52/0.70  # Training examples: 0 positive, 0 negative
% 0.52/0.70  # Parsed axioms                        : 20
% 0.52/0.70  # Removed by relevancy pruning/SinE    : 0
% 0.52/0.70  # Initial clauses                      : 40
% 0.52/0.70  # Removed in clause preprocessing      : 5
% 0.52/0.70  # Initial clauses in saturation        : 35
% 0.52/0.70  # Processed clauses                    : 2154
% 0.52/0.70  # ...of these trivial                  : 63
% 0.52/0.70  # ...subsumed                          : 1542
% 0.52/0.70  # ...remaining for further processing  : 549
% 0.52/0.70  # Other redundant clauses eliminated   : 2666
% 0.52/0.70  # Clauses deleted for lack of memory   : 0
% 0.52/0.70  # Backward-subsumed                    : 9
% 0.52/0.70  # Backward-rewritten                   : 141
% 0.52/0.70  # Generated clauses                    : 42173
% 0.52/0.70  # ...of the previous two non-trivial   : 34319
% 0.52/0.70  # Contextual simplify-reflections      : 23
% 0.52/0.70  # Paramodulations                      : 39454
% 0.52/0.70  # Factorizations                       : 4
% 0.52/0.70  # Equation resolutions                 : 2666
% 0.52/0.70  # Propositional unsat checks           : 0
% 0.52/0.70  #    Propositional check models        : 0
% 0.52/0.70  #    Propositional check unsatisfiable : 0
% 0.52/0.70  #    Propositional clauses             : 0
% 0.52/0.70  #    Propositional clauses after purity: 0
% 0.52/0.70  #    Propositional unsat core size     : 0
% 0.52/0.70  #    Propositional preprocessing time  : 0.000
% 0.52/0.70  #    Propositional encoding time       : 0.000
% 0.52/0.70  #    Propositional solver time         : 0.000
% 0.52/0.70  #    Success case prop preproc time    : 0.000
% 0.52/0.70  #    Success case prop encoding time   : 0.000
% 0.52/0.70  #    Success case prop solver time     : 0.000
% 0.52/0.70  # Current number of processed clauses  : 307
% 0.52/0.70  #    Positive orientable unit clauses  : 28
% 0.52/0.70  #    Positive unorientable unit clauses: 0
% 0.52/0.70  #    Negative unit clauses             : 3
% 0.52/0.70  #    Non-unit-clauses                  : 276
% 0.52/0.70  # Current number of unprocessed clauses: 32073
% 0.52/0.70  # ...number of literals in the above   : 118942
% 0.52/0.70  # Current number of archived formulas  : 0
% 0.52/0.70  # Current number of archived clauses   : 238
% 0.52/0.70  # Clause-clause subsumption calls (NU) : 34004
% 0.52/0.70  # Rec. Clause-clause subsumption calls : 23388
% 0.52/0.70  # Non-unit clause-clause subsumptions  : 1492
% 0.52/0.70  # Unit Clause-clause subsumption calls : 831
% 0.52/0.70  # Rewrite failures with RHS unbound    : 0
% 0.52/0.70  # BW rewrite match attempts            : 75
% 0.52/0.70  # BW rewrite match successes           : 32
% 0.52/0.70  # Condensation attempts                : 0
% 0.52/0.70  # Condensation successes               : 0
% 0.52/0.70  # Termbank termtop insertions          : 628367
% 0.52/0.70  
% 0.52/0.70  # -------------------------------------------------
% 0.52/0.70  # User time                : 0.340 s
% 0.52/0.70  # System time              : 0.022 s
% 0.52/0.70  # Total time               : 0.362 s
% 0.52/0.70  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
