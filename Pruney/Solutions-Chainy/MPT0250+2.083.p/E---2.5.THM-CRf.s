%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:18 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 231 expanded)
%              Number of clauses        :   33 (  89 expanded)
%              Number of leaves         :   14 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  146 ( 380 expanded)
%              Number of equality atoms :   70 ( 252 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
     => r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

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

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t98_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

fof(t99_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X1,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
       => r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t45_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X70,X71] : k3_tarski(k2_tarski(X70,X71)) = k2_xboole_0(X70,X71) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X18,X17)
        | X18 = X14
        | X18 = X15
        | X18 = X16
        | X17 != k1_enumset1(X14,X15,X16) )
      & ( X19 != X14
        | r2_hidden(X19,X17)
        | X17 != k1_enumset1(X14,X15,X16) )
      & ( X19 != X15
        | r2_hidden(X19,X17)
        | X17 != k1_enumset1(X14,X15,X16) )
      & ( X19 != X16
        | r2_hidden(X19,X17)
        | X17 != k1_enumset1(X14,X15,X16) )
      & ( esk2_4(X20,X21,X22,X23) != X20
        | ~ r2_hidden(esk2_4(X20,X21,X22,X23),X23)
        | X23 = k1_enumset1(X20,X21,X22) )
      & ( esk2_4(X20,X21,X22,X23) != X21
        | ~ r2_hidden(esk2_4(X20,X21,X22,X23),X23)
        | X23 = k1_enumset1(X20,X21,X22) )
      & ( esk2_4(X20,X21,X22,X23) != X22
        | ~ r2_hidden(esk2_4(X20,X21,X22,X23),X23)
        | X23 = k1_enumset1(X20,X21,X22) )
      & ( r2_hidden(esk2_4(X20,X21,X22,X23),X23)
        | esk2_4(X20,X21,X22,X23) = X20
        | esk2_4(X20,X21,X22,X23) = X21
        | esk2_4(X20,X21,X22,X23) = X22
        | X23 = k1_enumset1(X20,X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_18,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X31,X32,X33,X34] : k3_enumset1(X31,X31,X32,X33,X34) = k2_enumset1(X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,plain,(
    ! [X35,X36,X37,X38,X39] : k4_enumset1(X35,X35,X36,X37,X38,X39) = k3_enumset1(X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_21,plain,(
    ! [X40,X41,X42,X43,X44,X45] : k5_enumset1(X40,X40,X41,X42,X43,X44,X45) = k4_enumset1(X40,X41,X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_22,plain,(
    ! [X46,X47,X48,X49,X50,X51,X52] : k6_enumset1(X46,X46,X47,X48,X49,X50,X51,X52) = k5_enumset1(X46,X47,X48,X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_23,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk6_0),esk7_0),esk7_0)
    & ~ r2_hidden(esk6_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_24,plain,(
    ! [X25] : k2_tarski(X25,X25) = k1_tarski(X25) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_25,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_27,plain,(
    ! [X53,X54,X55] : k1_enumset1(X53,X54,X55) = k1_enumset1(X53,X55,X54) ),
    inference(variable_rename,[status(thm)],[t98_enumset1])).

fof(c_0_28,plain,(
    ! [X56,X57,X58] : k1_enumset1(X56,X57,X58) = k1_enumset1(X57,X56,X58) ),
    inference(variable_rename,[status(thm)],[t99_enumset1])).

fof(c_0_29,plain,(
    ! [X59,X60,X61,X63,X64,X65,X66,X68] :
      ( ( r2_hidden(X61,esk3_3(X59,X60,X61))
        | ~ r2_hidden(X61,X60)
        | X60 != k3_tarski(X59) )
      & ( r2_hidden(esk3_3(X59,X60,X61),X59)
        | ~ r2_hidden(X61,X60)
        | X60 != k3_tarski(X59) )
      & ( ~ r2_hidden(X63,X64)
        | ~ r2_hidden(X64,X59)
        | r2_hidden(X63,X60)
        | X60 != k3_tarski(X59) )
      & ( ~ r2_hidden(esk4_2(X65,X66),X66)
        | ~ r2_hidden(esk4_2(X65,X66),X68)
        | ~ r2_hidden(X68,X65)
        | X66 = k3_tarski(X65) )
      & ( r2_hidden(esk4_2(X65,X66),esk5_2(X65,X66))
        | r2_hidden(esk4_2(X65,X66),X66)
        | X66 = k3_tarski(X65) )
      & ( r2_hidden(esk5_2(X65,X66),X65)
        | r2_hidden(esk4_2(X65,X66),X66)
        | X66 = k3_tarski(X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk6_0),esk7_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_39,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_42,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)),esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_26]),c_0_38]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_45,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_46,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_2(X1,X2),k3_tarski(X3))
    | r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,plain,
    ( r2_hidden(esk1_2(X1,X2),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1)))
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk1_2(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),X1),esk7_0)
    | r1_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1),X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:59:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.19/0.41  # and selection function SelectNegativeLiterals.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.028 s
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t45_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 0.19/0.41  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.41  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.41  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.41  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.41  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.41  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.41  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.41  fof(t98_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 0.19/0.41  fof(t99_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X1,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 0.19/0.41  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 0.19/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.41  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2))), inference(assume_negation,[status(cth)],[t45_zfmisc_1])).
% 0.19/0.41  fof(c_0_15, plain, ![X70, X71]:k3_tarski(k2_tarski(X70,X71))=k2_xboole_0(X70,X71), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.41  fof(c_0_16, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.41  fof(c_0_17, plain, ![X14, X15, X16, X17, X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X18,X17)|(X18=X14|X18=X15|X18=X16)|X17!=k1_enumset1(X14,X15,X16))&(((X19!=X14|r2_hidden(X19,X17)|X17!=k1_enumset1(X14,X15,X16))&(X19!=X15|r2_hidden(X19,X17)|X17!=k1_enumset1(X14,X15,X16)))&(X19!=X16|r2_hidden(X19,X17)|X17!=k1_enumset1(X14,X15,X16))))&((((esk2_4(X20,X21,X22,X23)!=X20|~r2_hidden(esk2_4(X20,X21,X22,X23),X23)|X23=k1_enumset1(X20,X21,X22))&(esk2_4(X20,X21,X22,X23)!=X21|~r2_hidden(esk2_4(X20,X21,X22,X23),X23)|X23=k1_enumset1(X20,X21,X22)))&(esk2_4(X20,X21,X22,X23)!=X22|~r2_hidden(esk2_4(X20,X21,X22,X23),X23)|X23=k1_enumset1(X20,X21,X22)))&(r2_hidden(esk2_4(X20,X21,X22,X23),X23)|(esk2_4(X20,X21,X22,X23)=X20|esk2_4(X20,X21,X22,X23)=X21|esk2_4(X20,X21,X22,X23)=X22)|X23=k1_enumset1(X20,X21,X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.41  fof(c_0_18, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.41  fof(c_0_19, plain, ![X31, X32, X33, X34]:k3_enumset1(X31,X31,X32,X33,X34)=k2_enumset1(X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.41  fof(c_0_20, plain, ![X35, X36, X37, X38, X39]:k4_enumset1(X35,X35,X36,X37,X38,X39)=k3_enumset1(X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.41  fof(c_0_21, plain, ![X40, X41, X42, X43, X44, X45]:k5_enumset1(X40,X40,X41,X42,X43,X44,X45)=k4_enumset1(X40,X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.41  fof(c_0_22, plain, ![X46, X47, X48, X49, X50, X51, X52]:k6_enumset1(X46,X46,X47,X48,X49,X50,X51,X52)=k5_enumset1(X46,X47,X48,X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.41  fof(c_0_23, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk6_0),esk7_0),esk7_0)&~r2_hidden(esk6_0,esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.41  fof(c_0_24, plain, ![X25]:k2_tarski(X25,X25)=k1_tarski(X25), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.41  cnf(c_0_25, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  fof(c_0_27, plain, ![X53, X54, X55]:k1_enumset1(X53,X54,X55)=k1_enumset1(X53,X55,X54), inference(variable_rename,[status(thm)],[t98_enumset1])).
% 0.19/0.41  fof(c_0_28, plain, ![X56, X57, X58]:k1_enumset1(X56,X57,X58)=k1_enumset1(X57,X56,X58), inference(variable_rename,[status(thm)],[t99_enumset1])).
% 0.19/0.41  fof(c_0_29, plain, ![X59, X60, X61, X63, X64, X65, X66, X68]:((((r2_hidden(X61,esk3_3(X59,X60,X61))|~r2_hidden(X61,X60)|X60!=k3_tarski(X59))&(r2_hidden(esk3_3(X59,X60,X61),X59)|~r2_hidden(X61,X60)|X60!=k3_tarski(X59)))&(~r2_hidden(X63,X64)|~r2_hidden(X64,X59)|r2_hidden(X63,X60)|X60!=k3_tarski(X59)))&((~r2_hidden(esk4_2(X65,X66),X66)|(~r2_hidden(esk4_2(X65,X66),X68)|~r2_hidden(X68,X65))|X66=k3_tarski(X65))&((r2_hidden(esk4_2(X65,X66),esk5_2(X65,X66))|r2_hidden(esk4_2(X65,X66),X66)|X66=k3_tarski(X65))&(r2_hidden(esk5_2(X65,X66),X65)|r2_hidden(esk4_2(X65,X66),X66)|X66=k3_tarski(X65))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.19/0.41  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_33, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_34, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_35, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_36, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk6_0),esk7_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.41  cnf(c_0_37, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.41  cnf(c_0_38, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.41  cnf(c_0_39, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_40, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_41, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  fof(c_0_42, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.41  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)),esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_26]), c_0_38]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.19/0.41  cnf(c_0_45, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35])).
% 0.19/0.41  cnf(c_0_46, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35])).
% 0.19/0.41  cnf(c_0_47, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_41])).
% 0.19/0.41  cnf(c_0_48, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.41  cnf(c_0_49, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_43])).
% 0.19/0.41  cnf(c_0_50, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (r1_tarski(k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.19/0.41  cnf(c_0_52, plain, (r2_hidden(esk1_2(X1,X2),k3_tarski(X3))|r1_tarski(X1,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.41  cnf(c_0_53, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[c_0_49])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.41  cnf(c_0_55, plain, (r2_hidden(esk1_2(X1,X2),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1)))|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.41  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (r2_hidden(esk1_2(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),X1),esk7_0)|r1_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.41  cnf(c_0_58, plain, (r2_hidden(X1,X2)|~r1_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1),X2)), inference(spm,[status(thm)],[c_0_50, c_0_53])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (r1_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (~r2_hidden(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 62
% 0.19/0.41  # Proof object clause steps            : 33
% 0.19/0.41  # Proof object formula steps           : 29
% 0.19/0.41  # Proof object conjectures             : 11
% 0.19/0.41  # Proof object clause conjectures      : 8
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 17
% 0.19/0.41  # Proof object initial formulas used   : 14
% 0.19/0.41  # Proof object generating inferences   : 9
% 0.19/0.41  # Proof object simplifying inferences  : 58
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 14
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 29
% 0.19/0.41  # Removed in clause preprocessing      : 8
% 0.19/0.41  # Initial clauses in saturation        : 21
% 0.19/0.41  # Processed clauses                    : 388
% 0.19/0.41  # ...of these trivial                  : 4
% 0.19/0.41  # ...subsumed                          : 238
% 0.19/0.41  # ...remaining for further processing  : 146
% 0.19/0.41  # Other redundant clauses eliminated   : 10
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 0
% 0.19/0.41  # Backward-rewritten                   : 1
% 0.19/0.41  # Generated clauses                    : 1512
% 0.19/0.41  # ...of the previous two non-trivial   : 1436
% 0.19/0.41  # Contextual simplify-reflections      : 0
% 0.19/0.41  # Paramodulations                      : 1448
% 0.19/0.41  # Factorizations                       : 2
% 0.19/0.41  # Equation resolutions                 : 62
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 142
% 0.19/0.41  #    Positive orientable unit clauses  : 7
% 0.19/0.41  #    Positive unorientable unit clauses: 3
% 0.19/0.41  #    Negative unit clauses             : 1
% 0.19/0.41  #    Non-unit-clauses                  : 131
% 0.19/0.41  # Current number of unprocessed clauses: 1060
% 0.19/0.41  # ...number of literals in the above   : 4963
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 9
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 2720
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 2229
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 235
% 0.19/0.41  # Unit Clause-clause subsumption calls : 41
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 57
% 0.19/0.41  # BW rewrite match successes           : 52
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 35972
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.070 s
% 0.19/0.41  # System time              : 0.005 s
% 0.19/0.41  # Total time               : 0.075 s
% 0.19/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
