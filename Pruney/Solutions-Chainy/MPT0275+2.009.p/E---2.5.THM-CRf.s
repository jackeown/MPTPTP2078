%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:02 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 528 expanded)
%              Number of clauses        :   65 ( 223 expanded)
%              Number of leaves         :   18 ( 150 expanded)
%              Depth                    :   11
%              Number of atoms          :  260 (1370 expanded)
%              Number of equality atoms :  112 ( 745 expanded)
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

fof(t73_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

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

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t53_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r2_hidden(X3,X2) )
     => k3_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(c_0_18,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42,X43,X44,X45] :
      ( ( ~ r2_hidden(X40,X39)
        | X40 = X36
        | X40 = X37
        | X40 = X38
        | X39 != k1_enumset1(X36,X37,X38) )
      & ( X41 != X36
        | r2_hidden(X41,X39)
        | X39 != k1_enumset1(X36,X37,X38) )
      & ( X41 != X37
        | r2_hidden(X41,X39)
        | X39 != k1_enumset1(X36,X37,X38) )
      & ( X41 != X38
        | r2_hidden(X41,X39)
        | X39 != k1_enumset1(X36,X37,X38) )
      & ( esk3_4(X42,X43,X44,X45) != X42
        | ~ r2_hidden(esk3_4(X42,X43,X44,X45),X45)
        | X45 = k1_enumset1(X42,X43,X44) )
      & ( esk3_4(X42,X43,X44,X45) != X43
        | ~ r2_hidden(esk3_4(X42,X43,X44,X45),X45)
        | X45 = k1_enumset1(X42,X43,X44) )
      & ( esk3_4(X42,X43,X44,X45) != X44
        | ~ r2_hidden(esk3_4(X42,X43,X44,X45),X45)
        | X45 = k1_enumset1(X42,X43,X44) )
      & ( r2_hidden(esk3_4(X42,X43,X44,X45),X45)
        | esk3_4(X42,X43,X44,X45) = X42
        | esk3_4(X42,X43,X44,X45) = X43
        | esk3_4(X42,X43,X44,X45) = X44
        | X45 = k1_enumset1(X42,X43,X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_19,plain,(
    ! [X49,X50,X51] : k2_enumset1(X49,X49,X50,X51) = k1_enumset1(X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X52,X53,X54,X55] : k3_enumset1(X52,X52,X53,X54,X55) = k2_enumset1(X52,X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,plain,(
    ! [X56,X57,X58,X59,X60] : k4_enumset1(X56,X56,X57,X58,X59,X60) = k3_enumset1(X56,X57,X58,X59,X60) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_22,plain,(
    ! [X61,X62,X63,X64,X65,X66] : k5_enumset1(X61,X61,X62,X63,X64,X65,X66) = k4_enumset1(X61,X62,X63,X64,X65,X66) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t73_zfmisc_1])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,negated_conjecture,
    ( ( k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_xboole_0
      | ~ r2_hidden(esk4_0,esk6_0)
      | ~ r2_hidden(esk5_0,esk6_0) )
    & ( r2_hidden(esk4_0,esk6_0)
      | k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_xboole_0 )
    & ( r2_hidden(esk5_0,esk6_0)
      | k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])])).

fof(c_0_30,plain,(
    ! [X47,X48] : k1_enumset1(X47,X47,X48) = k2_tarski(X47,X48) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_31,plain,(
    ! [X32,X33] : k4_xboole_0(X32,X33) = k5_xboole_0(X32,k3_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_32,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | ~ r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X14)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X15)
        | X16 = k3_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X14)
        | r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k3_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X15)
        | r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k3_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_34,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r2_hidden(X19,X20)
        | ~ r2_hidden(X19,X21)
        | ~ r2_hidden(X19,k5_xboole_0(X20,X21)) )
      & ( r2_hidden(X19,X20)
        | r2_hidden(X19,X21)
        | ~ r2_hidden(X19,k5_xboole_0(X20,X21)) )
      & ( ~ r2_hidden(X19,X20)
        | r2_hidden(X19,X21)
        | r2_hidden(X19,k5_xboole_0(X20,X21)) )
      & ( ~ r2_hidden(X19,X21)
        | r2_hidden(X19,X20)
        | r2_hidden(X19,k5_xboole_0(X20,X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X4,X4,X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_39,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_40,plain,(
    ! [X22,X23,X25,X26,X27] :
      ( ( r1_xboole_0(X22,X23)
        | r2_hidden(esk2_2(X22,X23),k3_xboole_0(X22,X23)) )
      & ( ~ r2_hidden(X27,k3_xboole_0(X25,X26))
        | ~ r1_xboole_0(X25,X26) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_41,plain,(
    ! [X35] : r1_xboole_0(X35,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_42,plain,(
    ! [X34] : k3_xboole_0(X34,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).

cnf(c_0_48,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)) = k1_xboole_0
    | r2_hidden(esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_44])])).

cnf(c_0_55,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)) = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_37]),c_0_38]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k5_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X1,X3),X4))
    | r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) = k1_xboole_0
    | r2_hidden(esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X1,X4)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_xboole_0
    | ~ r2_hidden(esk4_0,esk6_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k5_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X3,X1),X4))
    | r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_46,c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_49])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X4,X1)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_65,plain,(
    ! [X67,X68,X69] :
      ( ~ r2_hidden(X67,X68)
      | ~ r2_hidden(X69,X68)
      | k3_xboole_0(k2_tarski(X67,X69),X68) = k2_tarski(X67,X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_zfmisc_1])])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk4_0,k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_69,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_71,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)) != k1_xboole_0
    | ~ r2_hidden(esk4_0,esk6_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_37]),c_0_38]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk5_0,k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_59]),c_0_64])).

cnf(c_0_73,plain,
    ( k3_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X2,X2,X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_76,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_69])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_70])).

fof(c_0_79,plain,(
    ! [X30,X31] :
      ( ( k4_xboole_0(X30,X31) != k1_xboole_0
        | r1_tarski(X30,X31) )
      & ( ~ r1_tarski(X30,X31)
        | k4_xboole_0(X30,X31) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_80,plain,(
    ! [X28,X29] :
      ( ( r1_tarski(X28,X29)
        | X28 != X29 )
      & ( r1_tarski(X29,X28)
        | X28 != X29 )
      & ( ~ r1_tarski(X28,X29)
        | ~ r1_tarski(X29,X28)
        | X28 = X29 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_81,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) != k1_xboole_0
    | ~ r2_hidden(esk4_0,esk6_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_49])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_72])).

cnf(c_0_83,plain,
    ( k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X3),X2) = k5_enumset1(X1,X1,X1,X1,X1,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_37]),c_0_37]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk4_0,k3_xboole_0(X1,esk6_0))
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_74])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_75])])).

cnf(c_0_86,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_77])).

cnf(c_0_87,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_78,c_0_77])).

cnf(c_0_88,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

fof(c_0_90,plain,(
    ! [X18] : k3_xboole_0(X18,X18) = X18 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_91,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) != k1_xboole_0
    | ~ r2_hidden(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_92,negated_conjecture,
    ( k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) = k5_enumset1(X1,X1,X1,X1,X1,X1,esk5_0)
    | ~ r2_hidden(X1,k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_72])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk4_0,k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_49])).

cnf(c_0_94,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_95,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_88,c_0_38])).

cnf(c_0_96,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_97,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_74])])).

cnf(c_0_99,negated_conjecture,
    ( k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) = k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_100,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_99]),c_0_100])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:20:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 3.09/3.29  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 3.09/3.29  # and selection function GSelectMinInfpos.
% 3.09/3.29  #
% 3.09/3.29  # Preprocessing time       : 0.028 s
% 3.09/3.29  # Presaturation interreduction done
% 3.09/3.29  
% 3.09/3.29  # Proof found!
% 3.09/3.29  # SZS status Theorem
% 3.09/3.29  # SZS output start CNFRefutation
% 3.09/3.29  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.09/3.29  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.09/3.29  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.09/3.29  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.09/3.29  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.09/3.29  fof(t73_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 3.09/3.29  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.09/3.29  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.09/3.29  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.09/3.29  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.09/3.29  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.09/3.29  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.09/3.29  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.09/3.29  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.09/3.29  fof(t53_zfmisc_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k3_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 3.09/3.29  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.09/3.29  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.09/3.29  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.09/3.29  fof(c_0_18, plain, ![X36, X37, X38, X39, X40, X41, X42, X43, X44, X45]:(((~r2_hidden(X40,X39)|(X40=X36|X40=X37|X40=X38)|X39!=k1_enumset1(X36,X37,X38))&(((X41!=X36|r2_hidden(X41,X39)|X39!=k1_enumset1(X36,X37,X38))&(X41!=X37|r2_hidden(X41,X39)|X39!=k1_enumset1(X36,X37,X38)))&(X41!=X38|r2_hidden(X41,X39)|X39!=k1_enumset1(X36,X37,X38))))&((((esk3_4(X42,X43,X44,X45)!=X42|~r2_hidden(esk3_4(X42,X43,X44,X45),X45)|X45=k1_enumset1(X42,X43,X44))&(esk3_4(X42,X43,X44,X45)!=X43|~r2_hidden(esk3_4(X42,X43,X44,X45),X45)|X45=k1_enumset1(X42,X43,X44)))&(esk3_4(X42,X43,X44,X45)!=X44|~r2_hidden(esk3_4(X42,X43,X44,X45),X45)|X45=k1_enumset1(X42,X43,X44)))&(r2_hidden(esk3_4(X42,X43,X44,X45),X45)|(esk3_4(X42,X43,X44,X45)=X42|esk3_4(X42,X43,X44,X45)=X43|esk3_4(X42,X43,X44,X45)=X44)|X45=k1_enumset1(X42,X43,X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 3.09/3.29  fof(c_0_19, plain, ![X49, X50, X51]:k2_enumset1(X49,X49,X50,X51)=k1_enumset1(X49,X50,X51), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 3.09/3.29  fof(c_0_20, plain, ![X52, X53, X54, X55]:k3_enumset1(X52,X52,X53,X54,X55)=k2_enumset1(X52,X53,X54,X55), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 3.09/3.29  fof(c_0_21, plain, ![X56, X57, X58, X59, X60]:k4_enumset1(X56,X56,X57,X58,X59,X60)=k3_enumset1(X56,X57,X58,X59,X60), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 3.09/3.29  fof(c_0_22, plain, ![X61, X62, X63, X64, X65, X66]:k5_enumset1(X61,X61,X62,X63,X64,X65,X66)=k4_enumset1(X61,X62,X63,X64,X65,X66), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 3.09/3.29  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3)))), inference(assume_negation,[status(cth)],[t73_zfmisc_1])).
% 3.09/3.29  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.09/3.29  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.09/3.29  cnf(c_0_26, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.09/3.29  cnf(c_0_27, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.09/3.29  cnf(c_0_28, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.09/3.29  fof(c_0_29, negated_conjecture, ((k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_xboole_0|(~r2_hidden(esk4_0,esk6_0)|~r2_hidden(esk5_0,esk6_0)))&((r2_hidden(esk4_0,esk6_0)|k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_xboole_0)&(r2_hidden(esk5_0,esk6_0)|k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])])).
% 3.09/3.29  fof(c_0_30, plain, ![X47, X48]:k1_enumset1(X47,X47,X48)=k2_tarski(X47,X48), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 3.09/3.29  fof(c_0_31, plain, ![X32, X33]:k4_xboole_0(X32,X33)=k5_xboole_0(X32,k3_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 3.09/3.29  fof(c_0_32, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k3_xboole_0(X9,X10))&(r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k3_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|~r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k3_xboole_0(X9,X10)))&((~r2_hidden(esk1_3(X14,X15,X16),X16)|(~r2_hidden(esk1_3(X14,X15,X16),X14)|~r2_hidden(esk1_3(X14,X15,X16),X15))|X16=k3_xboole_0(X14,X15))&((r2_hidden(esk1_3(X14,X15,X16),X14)|r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k3_xboole_0(X14,X15))&(r2_hidden(esk1_3(X14,X15,X16),X15)|r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k3_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 3.09/3.29  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.09/3.29  fof(c_0_34, plain, ![X19, X20, X21]:(((~r2_hidden(X19,X20)|~r2_hidden(X19,X21)|~r2_hidden(X19,k5_xboole_0(X20,X21)))&(r2_hidden(X19,X20)|r2_hidden(X19,X21)|~r2_hidden(X19,k5_xboole_0(X20,X21))))&((~r2_hidden(X19,X20)|r2_hidden(X19,X21)|r2_hidden(X19,k5_xboole_0(X20,X21)))&(~r2_hidden(X19,X21)|r2_hidden(X19,X20)|r2_hidden(X19,k5_xboole_0(X20,X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 3.09/3.29  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X4,X4,X4,X4,X2,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 3.09/3.29  cnf(c_0_36, negated_conjecture, (r2_hidden(esk4_0,esk6_0)|k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.09/3.29  cnf(c_0_37, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.09/3.29  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.09/3.29  fof(c_0_39, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 3.09/3.29  fof(c_0_40, plain, ![X22, X23, X25, X26, X27]:((r1_xboole_0(X22,X23)|r2_hidden(esk2_2(X22,X23),k3_xboole_0(X22,X23)))&(~r2_hidden(X27,k3_xboole_0(X25,X26))|~r1_xboole_0(X25,X26))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 3.09/3.29  fof(c_0_41, plain, ![X35]:r1_xboole_0(X35,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 3.09/3.29  fof(c_0_42, plain, ![X34]:k3_xboole_0(X34,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 3.09/3.29  cnf(c_0_43, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.09/3.29  cnf(c_0_44, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 3.09/3.29  cnf(c_0_45, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.09/3.29  cnf(c_0_46, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.09/3.29  cnf(c_0_47, plain, (r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X1,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).
% 3.09/3.29  cnf(c_0_48, negated_conjecture, (k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))=k1_xboole_0|r2_hidden(esk4_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 3.09/3.29  cnf(c_0_49, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 3.09/3.29  cnf(c_0_50, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 3.09/3.29  cnf(c_0_51, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 3.09/3.29  cnf(c_0_52, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.09/3.29  cnf(c_0_53, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_43])).
% 3.09/3.29  cnf(c_0_54, plain, (r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_44])])).
% 3.09/3.29  cnf(c_0_55, negated_conjecture, (k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_37]), c_0_38]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 3.09/3.29  cnf(c_0_56, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.09/3.29  cnf(c_0_57, plain, (r2_hidden(X1,k5_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X1,X3),X4))|r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 3.09/3.29  cnf(c_0_58, negated_conjecture, (k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))=k1_xboole_0|r2_hidden(esk4_0,esk6_0)), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 3.09/3.29  cnf(c_0_59, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 3.09/3.29  cnf(c_0_60, plain, (r2_hidden(X1,k3_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X1,X4)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_53, c_0_47])).
% 3.09/3.29  cnf(c_0_61, negated_conjecture, (k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_xboole_0|~r2_hidden(esk4_0,esk6_0)|~r2_hidden(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.09/3.29  cnf(c_0_62, plain, (r2_hidden(X1,k5_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X3,X1),X4))|r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_46, c_0_54])).
% 3.09/3.29  cnf(c_0_63, negated_conjecture, (k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_55, c_0_49])).
% 3.09/3.29  cnf(c_0_64, plain, (r2_hidden(X1,k3_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X4,X1)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 3.09/3.29  fof(c_0_65, plain, ![X67, X68, X69]:(~r2_hidden(X67,X68)|~r2_hidden(X69,X68)|k3_xboole_0(k2_tarski(X67,X69),X68)=k2_tarski(X67,X69)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_zfmisc_1])])).
% 3.09/3.29  cnf(c_0_66, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_56])).
% 3.09/3.29  cnf(c_0_67, negated_conjecture, (r2_hidden(esk4_0,k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_60])).
% 3.09/3.29  cnf(c_0_68, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.09/3.29  cnf(c_0_69, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.09/3.29  cnf(c_0_70, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.09/3.29  cnf(c_0_71, negated_conjecture, (k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))!=k1_xboole_0|~r2_hidden(esk4_0,esk6_0)|~r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_37]), c_0_38]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 3.09/3.29  cnf(c_0_72, negated_conjecture, (r2_hidden(esk5_0,k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_59]), c_0_64])).
% 3.09/3.29  cnf(c_0_73, plain, (k3_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 3.09/3.29  cnf(c_0_74, negated_conjecture, (r2_hidden(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 3.09/3.29  cnf(c_0_75, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X2,X2,X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 3.09/3.29  cnf(c_0_76, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.09/3.29  cnf(c_0_77, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_69])).
% 3.09/3.29  cnf(c_0_78, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_70])).
% 3.09/3.29  fof(c_0_79, plain, ![X30, X31]:((k4_xboole_0(X30,X31)!=k1_xboole_0|r1_tarski(X30,X31))&(~r1_tarski(X30,X31)|k4_xboole_0(X30,X31)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 3.09/3.29  fof(c_0_80, plain, ![X28, X29]:(((r1_tarski(X28,X29)|X28!=X29)&(r1_tarski(X29,X28)|X28!=X29))&(~r1_tarski(X28,X29)|~r1_tarski(X29,X28)|X28=X29)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 3.09/3.29  cnf(c_0_81, negated_conjecture, (k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))!=k1_xboole_0|~r2_hidden(esk4_0,esk6_0)|~r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_71, c_0_49])).
% 3.09/3.29  cnf(c_0_82, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_66, c_0_72])).
% 3.09/3.29  cnf(c_0_83, plain, (k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X3),X2)=k5_enumset1(X1,X1,X1,X1,X1,X1,X3)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_37]), c_0_37]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 3.09/3.29  cnf(c_0_84, negated_conjecture, (r2_hidden(esk4_0,k3_xboole_0(X1,esk6_0))|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_53, c_0_74])).
% 3.09/3.29  cnf(c_0_85, plain, (r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_75])])).
% 3.09/3.29  cnf(c_0_86, plain, (k3_xboole_0(X1,X2)=X2|~r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_77])).
% 3.09/3.29  cnf(c_0_87, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,X3)|r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_78, c_0_77])).
% 3.09/3.29  cnf(c_0_88, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 3.09/3.29  cnf(c_0_89, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_80])).
% 3.09/3.29  fof(c_0_90, plain, ![X18]:k3_xboole_0(X18,X18)=X18, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 3.09/3.29  cnf(c_0_91, negated_conjecture, (k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))!=k1_xboole_0|~r2_hidden(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82])])).
% 3.09/3.29  cnf(c_0_92, negated_conjecture, (k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))=k5_enumset1(X1,X1,X1,X1,X1,X1,esk5_0)|~r2_hidden(X1,k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_83, c_0_72])).
% 3.09/3.29  cnf(c_0_93, negated_conjecture, (r2_hidden(esk4_0,k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_49])).
% 3.09/3.29  cnf(c_0_94, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 3.09/3.29  cnf(c_0_95, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_88, c_0_38])).
% 3.09/3.29  cnf(c_0_96, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_89])).
% 3.09/3.29  cnf(c_0_97, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_90])).
% 3.09/3.29  cnf(c_0_98, negated_conjecture, (k5_xboole_0(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_74])])).
% 3.09/3.29  cnf(c_0_99, negated_conjecture, (k3_xboole_0(esk6_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))=k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])).
% 3.09/3.29  cnf(c_0_100, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97])).
% 3.09/3.29  cnf(c_0_101, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_99]), c_0_100])]), ['proof']).
% 3.09/3.29  # SZS output end CNFRefutation
% 3.09/3.29  # Proof object total steps             : 102
% 3.09/3.29  # Proof object clause steps            : 65
% 3.09/3.29  # Proof object formula steps           : 37
% 3.09/3.29  # Proof object conjectures             : 23
% 3.09/3.29  # Proof object clause conjectures      : 20
% 3.09/3.29  # Proof object formula conjectures     : 3
% 3.09/3.29  # Proof object initial clauses used    : 26
% 3.09/3.29  # Proof object initial formulas used   : 18
% 3.09/3.29  # Proof object generating inferences   : 18
% 3.09/3.29  # Proof object simplifying inferences  : 82
% 3.09/3.29  # Training examples: 0 positive, 0 negative
% 3.09/3.29  # Parsed axioms                        : 18
% 3.09/3.29  # Removed by relevancy pruning/SinE    : 0
% 3.09/3.29  # Initial clauses                      : 39
% 3.09/3.29  # Removed in clause preprocessing      : 6
% 3.09/3.29  # Initial clauses in saturation        : 33
% 3.09/3.29  # Processed clauses                    : 6068
% 3.09/3.29  # ...of these trivial                  : 230
% 3.09/3.29  # ...subsumed                          : 3830
% 3.09/3.29  # ...remaining for further processing  : 2008
% 3.09/3.29  # Other redundant clauses eliminated   : 283
% 3.09/3.29  # Clauses deleted for lack of memory   : 0
% 3.09/3.29  # Backward-subsumed                    : 13
% 3.09/3.29  # Backward-rewritten                   : 907
% 3.09/3.29  # Generated clauses                    : 147105
% 3.09/3.29  # ...of the previous two non-trivial   : 130155
% 3.09/3.29  # Contextual simplify-reflections      : 5
% 3.09/3.29  # Paramodulations                      : 146604
% 3.09/3.29  # Factorizations                       : 221
% 3.09/3.29  # Equation resolutions                 : 283
% 3.09/3.29  # Propositional unsat checks           : 0
% 3.09/3.29  #    Propositional check models        : 0
% 3.09/3.29  #    Propositional check unsatisfiable : 0
% 3.09/3.29  #    Propositional clauses             : 0
% 3.09/3.29  #    Propositional clauses after purity: 0
% 3.09/3.29  #    Propositional unsat core size     : 0
% 3.09/3.29  #    Propositional preprocessing time  : 0.000
% 3.09/3.29  #    Propositional encoding time       : 0.000
% 3.09/3.29  #    Propositional solver time         : 0.000
% 3.09/3.29  #    Success case prop preproc time    : 0.000
% 3.09/3.29  #    Success case prop encoding time   : 0.000
% 3.09/3.29  #    Success case prop solver time     : 0.000
% 3.09/3.29  # Current number of processed clauses  : 1047
% 3.09/3.29  #    Positive orientable unit clauses  : 128
% 3.09/3.29  #    Positive unorientable unit clauses: 1
% 3.09/3.29  #    Negative unit clauses             : 32
% 3.09/3.29  #    Non-unit-clauses                  : 886
% 3.09/3.29  # Current number of unprocessed clauses: 121631
% 3.09/3.29  # ...number of literals in the above   : 806071
% 3.09/3.29  # Current number of archived formulas  : 0
% 3.09/3.29  # Current number of archived clauses   : 958
% 3.09/3.29  # Clause-clause subsumption calls (NU) : 243263
% 3.09/3.29  # Rec. Clause-clause subsumption calls : 197743
% 3.09/3.29  # Non-unit clause-clause subsumptions  : 2625
% 3.09/3.29  # Unit Clause-clause subsumption calls : 21402
% 3.09/3.29  # Rewrite failures with RHS unbound    : 0
% 3.09/3.29  # BW rewrite match attempts            : 619
% 3.09/3.29  # BW rewrite match successes           : 64
% 3.09/3.29  # Condensation attempts                : 0
% 3.09/3.29  # Condensation successes               : 0
% 3.09/3.29  # Termbank termtop insertions          : 4097612
% 3.09/3.29  
% 3.09/3.29  # -------------------------------------------------
% 3.09/3.29  # User time                : 2.888 s
% 3.09/3.29  # System time              : 0.068 s
% 3.09/3.29  # Total time               : 2.957 s
% 3.09/3.29  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
