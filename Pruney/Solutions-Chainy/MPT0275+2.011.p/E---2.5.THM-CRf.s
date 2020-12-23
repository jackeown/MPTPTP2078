%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:02 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 416 expanded)
%              Number of clauses        :   49 ( 177 expanded)
%              Number of leaves         :   15 ( 117 expanded)
%              Depth                    :   10
%              Number of atoms          :  211 (1078 expanded)
%              Number of equality atoms :   91 ( 585 expanded)
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

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(c_0_15,plain,(
    ! [X31,X32,X33,X34,X35,X36,X37,X38,X39,X40] :
      ( ( ~ r2_hidden(X35,X34)
        | X35 = X31
        | X35 = X32
        | X35 = X33
        | X34 != k1_enumset1(X31,X32,X33) )
      & ( X36 != X31
        | r2_hidden(X36,X34)
        | X34 != k1_enumset1(X31,X32,X33) )
      & ( X36 != X32
        | r2_hidden(X36,X34)
        | X34 != k1_enumset1(X31,X32,X33) )
      & ( X36 != X33
        | r2_hidden(X36,X34)
        | X34 != k1_enumset1(X31,X32,X33) )
      & ( esk3_4(X37,X38,X39,X40) != X37
        | ~ r2_hidden(esk3_4(X37,X38,X39,X40),X40)
        | X40 = k1_enumset1(X37,X38,X39) )
      & ( esk3_4(X37,X38,X39,X40) != X38
        | ~ r2_hidden(esk3_4(X37,X38,X39,X40),X40)
        | X40 = k1_enumset1(X37,X38,X39) )
      & ( esk3_4(X37,X38,X39,X40) != X39
        | ~ r2_hidden(esk3_4(X37,X38,X39,X40),X40)
        | X40 = k1_enumset1(X37,X38,X39) )
      & ( r2_hidden(esk3_4(X37,X38,X39,X40),X40)
        | esk3_4(X37,X38,X39,X40) = X37
        | esk3_4(X37,X38,X39,X40) = X38
        | esk3_4(X37,X38,X39,X40) = X39
        | X40 = k1_enumset1(X37,X38,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_16,plain,(
    ! [X44,X45,X46] : k2_enumset1(X44,X44,X45,X46) = k1_enumset1(X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X47,X48,X49,X50] : k3_enumset1(X47,X47,X48,X49,X50) = k2_enumset1(X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_18,plain,(
    ! [X51,X52,X53,X54,X55] : k4_enumset1(X51,X51,X52,X53,X54,X55) = k3_enumset1(X51,X52,X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t73_zfmisc_1])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,negated_conjecture,
    ( ( k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_xboole_0
      | ~ r2_hidden(esk4_0,esk6_0)
      | ~ r2_hidden(esk5_0,esk6_0) )
    & ( r2_hidden(esk4_0,esk6_0)
      | k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_xboole_0 )
    & ( r2_hidden(esk5_0,esk6_0)
      | k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])])).

fof(c_0_25,plain,(
    ! [X42,X43] : k1_enumset1(X42,X42,X43) = k2_tarski(X42,X43) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_26,plain,(
    ! [X26,X27] : k4_xboole_0(X26,X27) = k5_xboole_0(X26,k3_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_27,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X11,X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | ~ r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X14)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_28,plain,(
    ! [X17,X18,X19] :
      ( ( ~ r2_hidden(X17,X18)
        | ~ r2_hidden(X17,X19)
        | ~ r2_hidden(X17,k5_xboole_0(X18,X19)) )
      & ( r2_hidden(X17,X18)
        | r2_hidden(X17,X19)
        | ~ r2_hidden(X17,k5_xboole_0(X18,X19)) )
      & ( ~ r2_hidden(X17,X18)
        | r2_hidden(X17,X19)
        | r2_hidden(X17,k5_xboole_0(X18,X19)) )
      & ( ~ r2_hidden(X17,X19)
        | r2_hidden(X17,X18)
        | r2_hidden(X17,k5_xboole_0(X18,X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_34,plain,(
    ! [X20,X21,X23,X24,X25] :
      ( ( r1_xboole_0(X20,X21)
        | r2_hidden(esk2_2(X20,X21),k3_xboole_0(X20,X21)) )
      & ( ~ r2_hidden(X25,k3_xboole_0(X23,X24))
        | ~ r1_xboole_0(X23,X24) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_35,plain,(
    ! [X29] : r1_xboole_0(X29,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_36,plain,(
    ! [X28] : k3_xboole_0(X28,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k4_enumset1(X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).

cnf(c_0_42,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)) = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X4,X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X2,X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_xboole_0
    | ~ r2_hidden(esk4_0,esk6_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X3,X1),X4))
    | r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,k4_enumset1(X3,X3,X3,X3,X4,X1)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_41])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k4_enumset1(X2,X2,X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)) = k1_xboole_0
    | r2_hidden(esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_31]),c_0_32]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k4_enumset1(X1,X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).

fof(c_0_60,plain,(
    ! [X56,X57,X58] :
      ( ~ r2_hidden(X56,X57)
      | ~ r2_hidden(X58,X57)
      | k3_xboole_0(k2_tarski(X56,X58),X57) = k2_tarski(X56,X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_zfmisc_1])])).

cnf(c_0_61,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)) != k1_xboole_0
    | ~ r2_hidden(esk4_0,esk6_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_31]),c_0_32]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk5_0,k3_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X1,X3),X4))
    | r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_40,c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) = k1_xboole_0
    | r2_hidden(esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_43])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,k4_enumset1(X1,X1,X1,X1,X3,X4)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_59])).

cnf(c_0_67,plain,
    ( k3_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) != k1_xboole_0
    | ~ r2_hidden(esk4_0,esk6_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_43])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk4_0,k3_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_55]),c_0_66])).

cnf(c_0_71,plain,
    ( k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X3),X2) = k4_enumset1(X1,X1,X1,X1,X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_31]),c_0_31]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_72,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) != k1_xboole_0
    | ~ r2_hidden(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( k3_xboole_0(esk6_0,k4_enumset1(X1,X1,X1,X1,X1,esk5_0)) = k4_enumset1(X1,X1,X1,X1,X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_69]),c_0_43])).

fof(c_0_75,plain,(
    ! [X30] : k5_xboole_0(X30,X30) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])])).

cnf(c_0_77,negated_conjecture,
    ( k3_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) = k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_73])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_78])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:09:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 3.59/3.82  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 3.59/3.82  # and selection function GSelectMinInfpos.
% 3.59/3.82  #
% 3.59/3.82  # Preprocessing time       : 0.028 s
% 3.59/3.82  # Presaturation interreduction done
% 3.59/3.82  
% 3.59/3.82  # Proof found!
% 3.59/3.82  # SZS status Theorem
% 3.59/3.82  # SZS output start CNFRefutation
% 3.59/3.82  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.59/3.82  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.59/3.82  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.59/3.82  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.59/3.82  fof(t73_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 3.59/3.82  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.59/3.82  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.59/3.82  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.59/3.82  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.59/3.82  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.59/3.82  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.59/3.82  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.59/3.82  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.59/3.82  fof(t53_zfmisc_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k3_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 3.59/3.82  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.59/3.82  fof(c_0_15, plain, ![X31, X32, X33, X34, X35, X36, X37, X38, X39, X40]:(((~r2_hidden(X35,X34)|(X35=X31|X35=X32|X35=X33)|X34!=k1_enumset1(X31,X32,X33))&(((X36!=X31|r2_hidden(X36,X34)|X34!=k1_enumset1(X31,X32,X33))&(X36!=X32|r2_hidden(X36,X34)|X34!=k1_enumset1(X31,X32,X33)))&(X36!=X33|r2_hidden(X36,X34)|X34!=k1_enumset1(X31,X32,X33))))&((((esk3_4(X37,X38,X39,X40)!=X37|~r2_hidden(esk3_4(X37,X38,X39,X40),X40)|X40=k1_enumset1(X37,X38,X39))&(esk3_4(X37,X38,X39,X40)!=X38|~r2_hidden(esk3_4(X37,X38,X39,X40),X40)|X40=k1_enumset1(X37,X38,X39)))&(esk3_4(X37,X38,X39,X40)!=X39|~r2_hidden(esk3_4(X37,X38,X39,X40),X40)|X40=k1_enumset1(X37,X38,X39)))&(r2_hidden(esk3_4(X37,X38,X39,X40),X40)|(esk3_4(X37,X38,X39,X40)=X37|esk3_4(X37,X38,X39,X40)=X38|esk3_4(X37,X38,X39,X40)=X39)|X40=k1_enumset1(X37,X38,X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 3.59/3.82  fof(c_0_16, plain, ![X44, X45, X46]:k2_enumset1(X44,X44,X45,X46)=k1_enumset1(X44,X45,X46), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 3.59/3.82  fof(c_0_17, plain, ![X47, X48, X49, X50]:k3_enumset1(X47,X47,X48,X49,X50)=k2_enumset1(X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 3.59/3.82  fof(c_0_18, plain, ![X51, X52, X53, X54, X55]:k4_enumset1(X51,X51,X52,X53,X54,X55)=k3_enumset1(X51,X52,X53,X54,X55), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 3.59/3.82  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3)))), inference(assume_negation,[status(cth)],[t73_zfmisc_1])).
% 3.59/3.82  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.59/3.82  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.59/3.82  cnf(c_0_22, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.59/3.82  cnf(c_0_23, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.59/3.82  fof(c_0_24, negated_conjecture, ((k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_xboole_0|(~r2_hidden(esk4_0,esk6_0)|~r2_hidden(esk5_0,esk6_0)))&((r2_hidden(esk4_0,esk6_0)|k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_xboole_0)&(r2_hidden(esk5_0,esk6_0)|k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])])).
% 3.59/3.82  fof(c_0_25, plain, ![X42, X43]:k1_enumset1(X42,X42,X43)=k2_tarski(X42,X43), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 3.59/3.82  fof(c_0_26, plain, ![X26, X27]:k4_xboole_0(X26,X27)=k5_xboole_0(X26,k3_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 3.59/3.82  fof(c_0_27, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9))&(r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|~r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k3_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|~r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k3_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))&(r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 3.59/3.82  fof(c_0_28, plain, ![X17, X18, X19]:(((~r2_hidden(X17,X18)|~r2_hidden(X17,X19)|~r2_hidden(X17,k5_xboole_0(X18,X19)))&(r2_hidden(X17,X18)|r2_hidden(X17,X19)|~r2_hidden(X17,k5_xboole_0(X18,X19))))&((~r2_hidden(X17,X18)|r2_hidden(X17,X19)|r2_hidden(X17,k5_xboole_0(X18,X19)))&(~r2_hidden(X17,X19)|r2_hidden(X17,X18)|r2_hidden(X17,k5_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 3.59/3.82  cnf(c_0_29, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])).
% 3.59/3.82  cnf(c_0_30, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.59/3.82  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.59/3.82  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 3.59/3.82  fof(c_0_33, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 3.59/3.82  fof(c_0_34, plain, ![X20, X21, X23, X24, X25]:((r1_xboole_0(X20,X21)|r2_hidden(esk2_2(X20,X21),k3_xboole_0(X20,X21)))&(~r2_hidden(X25,k3_xboole_0(X23,X24))|~r1_xboole_0(X23,X24))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 3.59/3.82  fof(c_0_35, plain, ![X29]:r1_xboole_0(X29,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 3.59/3.82  fof(c_0_36, plain, ![X28]:k3_xboole_0(X28,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 3.59/3.82  cnf(c_0_37, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.59/3.82  cnf(c_0_38, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.59/3.82  cnf(c_0_39, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.59/3.82  cnf(c_0_40, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.59/3.82  cnf(c_0_41, plain, (r2_hidden(X1,k4_enumset1(X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).
% 3.59/3.82  cnf(c_0_42, negated_conjecture, (k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 3.59/3.82  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 3.59/3.82  cnf(c_0_44, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.59/3.82  cnf(c_0_45, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 3.59/3.82  cnf(c_0_46, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.59/3.82  cnf(c_0_47, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_37])).
% 3.59/3.82  cnf(c_0_48, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X4,X4,X4,X2,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_21]), c_0_22]), c_0_23])).
% 3.59/3.82  cnf(c_0_49, negated_conjecture, (r2_hidden(esk4_0,esk6_0)|k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.59/3.82  cnf(c_0_50, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X2,X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_21]), c_0_22]), c_0_23])).
% 3.59/3.82  cnf(c_0_51, negated_conjecture, (k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_xboole_0|~r2_hidden(esk4_0,esk6_0)|~r2_hidden(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.59/3.82  cnf(c_0_52, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.59/3.82  cnf(c_0_53, plain, (r2_hidden(X1,k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X3,X1),X4))|r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 3.59/3.82  cnf(c_0_54, negated_conjecture, (k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 3.59/3.82  cnf(c_0_55, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 3.59/3.82  cnf(c_0_56, plain, (r2_hidden(X1,k3_xboole_0(X2,k4_enumset1(X3,X3,X3,X3,X4,X1)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_41])).
% 3.59/3.82  cnf(c_0_57, plain, (r2_hidden(X1,k4_enumset1(X2,X2,X2,X2,X1,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).
% 3.59/3.82  cnf(c_0_58, negated_conjecture, (k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))=k1_xboole_0|r2_hidden(esk4_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_31]), c_0_32]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 3.59/3.82  cnf(c_0_59, plain, (r2_hidden(X1,k4_enumset1(X1,X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).
% 3.59/3.82  fof(c_0_60, plain, ![X56, X57, X58]:(~r2_hidden(X56,X57)|~r2_hidden(X58,X57)|k3_xboole_0(k2_tarski(X56,X58),X57)=k2_tarski(X56,X58)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_zfmisc_1])])).
% 3.59/3.82  cnf(c_0_61, negated_conjecture, (k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))!=k1_xboole_0|~r2_hidden(esk4_0,esk6_0)|~r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_31]), c_0_32]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 3.59/3.82  cnf(c_0_62, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_52])).
% 3.59/3.82  cnf(c_0_63, negated_conjecture, (r2_hidden(esk5_0,k3_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56])).
% 3.59/3.82  cnf(c_0_64, plain, (r2_hidden(X1,k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X1,X3),X4))|r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_40, c_0_57])).
% 3.59/3.82  cnf(c_0_65, negated_conjecture, (k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))=k1_xboole_0|r2_hidden(esk4_0,esk6_0)), inference(rw,[status(thm)],[c_0_58, c_0_43])).
% 3.59/3.82  cnf(c_0_66, plain, (r2_hidden(X1,k3_xboole_0(X2,k4_enumset1(X1,X1,X1,X1,X3,X4)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_59])).
% 3.59/3.82  cnf(c_0_67, plain, (k3_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 3.59/3.82  cnf(c_0_68, negated_conjecture, (k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))!=k1_xboole_0|~r2_hidden(esk4_0,esk6_0)|~r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_61, c_0_43])).
% 3.59/3.82  cnf(c_0_69, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 3.59/3.82  cnf(c_0_70, negated_conjecture, (r2_hidden(esk4_0,k3_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_55]), c_0_66])).
% 3.59/3.82  cnf(c_0_71, plain, (k3_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X3),X2)=k4_enumset1(X1,X1,X1,X1,X1,X3)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_31]), c_0_31]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 3.59/3.82  cnf(c_0_72, negated_conjecture, (k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))!=k1_xboole_0|~r2_hidden(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69])])).
% 3.59/3.82  cnf(c_0_73, negated_conjecture, (r2_hidden(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_62, c_0_70])).
% 3.59/3.82  cnf(c_0_74, negated_conjecture, (k3_xboole_0(esk6_0,k4_enumset1(X1,X1,X1,X1,X1,esk5_0))=k4_enumset1(X1,X1,X1,X1,X1,esk5_0)|~r2_hidden(X1,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_69]), c_0_43])).
% 3.59/3.82  fof(c_0_75, plain, ![X30]:k5_xboole_0(X30,X30)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 3.59/3.82  cnf(c_0_76, negated_conjecture, (k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73])])).
% 3.59/3.82  cnf(c_0_77, negated_conjecture, (k3_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))=k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_74, c_0_73])).
% 3.59/3.82  cnf(c_0_78, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_75])).
% 3.59/3.82  cnf(c_0_79, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77]), c_0_78])]), ['proof']).
% 3.59/3.82  # SZS output end CNFRefutation
% 3.59/3.82  # Proof object total steps             : 80
% 3.59/3.82  # Proof object clause steps            : 49
% 3.59/3.82  # Proof object formula steps           : 31
% 3.59/3.82  # Proof object conjectures             : 21
% 3.59/3.82  # Proof object clause conjectures      : 18
% 3.59/3.82  # Proof object formula conjectures     : 3
% 3.59/3.82  # Proof object initial clauses used    : 20
% 3.59/3.82  # Proof object initial formulas used   : 15
% 3.59/3.82  # Proof object generating inferences   : 11
% 3.59/3.82  # Proof object simplifying inferences  : 65
% 3.59/3.82  # Training examples: 0 positive, 0 negative
% 3.59/3.82  # Parsed axioms                        : 15
% 3.59/3.82  # Removed by relevancy pruning/SinE    : 0
% 3.59/3.82  # Initial clauses                      : 33
% 3.59/3.82  # Removed in clause preprocessing      : 5
% 3.59/3.82  # Initial clauses in saturation        : 28
% 3.59/3.82  # Processed clauses                    : 6000
% 3.59/3.82  # ...of these trivial                  : 235
% 3.59/3.82  # ...subsumed                          : 3935
% 3.59/3.82  # ...remaining for further processing  : 1830
% 3.59/3.82  # Other redundant clauses eliminated   : 165
% 3.59/3.82  # Clauses deleted for lack of memory   : 0
% 3.59/3.82  # Backward-subsumed                    : 4
% 3.59/3.82  # Backward-rewritten                   : 671
% 3.59/3.82  # Generated clauses                    : 162625
% 3.59/3.82  # ...of the previous two non-trivial   : 146843
% 3.59/3.82  # Contextual simplify-reflections      : 5
% 3.59/3.82  # Paramodulations                      : 162250
% 3.59/3.82  # Factorizations                       : 213
% 3.59/3.82  # Equation resolutions                 : 165
% 3.59/3.82  # Propositional unsat checks           : 0
% 3.59/3.82  #    Propositional check models        : 0
% 3.59/3.82  #    Propositional check unsatisfiable : 0
% 3.59/3.82  #    Propositional clauses             : 0
% 3.59/3.82  #    Propositional clauses after purity: 0
% 3.59/3.82  #    Propositional unsat core size     : 0
% 3.59/3.82  #    Propositional preprocessing time  : 0.000
% 3.59/3.82  #    Propositional encoding time       : 0.000
% 3.59/3.82  #    Propositional solver time         : 0.000
% 3.59/3.82  #    Success case prop preproc time    : 0.000
% 3.59/3.82  #    Success case prop encoding time   : 0.000
% 3.59/3.82  #    Success case prop solver time     : 0.000
% 3.59/3.82  # Current number of processed clauses  : 1120
% 3.59/3.82  #    Positive orientable unit clauses  : 129
% 3.59/3.82  #    Positive unorientable unit clauses: 1
% 3.59/3.82  #    Negative unit clauses             : 72
% 3.59/3.82  #    Non-unit-clauses                  : 918
% 3.59/3.82  # Current number of unprocessed clauses: 137648
% 3.59/3.82  # ...number of literals in the above   : 949984
% 3.59/3.82  # Current number of archived formulas  : 0
% 3.59/3.82  # Current number of archived clauses   : 708
% 3.59/3.82  # Clause-clause subsumption calls (NU) : 320518
% 3.59/3.82  # Rec. Clause-clause subsumption calls : 245775
% 3.59/3.82  # Non-unit clause-clause subsumptions  : 2513
% 3.59/3.82  # Unit Clause-clause subsumption calls : 25032
% 3.59/3.82  # Rewrite failures with RHS unbound    : 0
% 3.59/3.82  # BW rewrite match attempts            : 419
% 3.59/3.82  # BW rewrite match successes           : 43
% 3.59/3.82  # Condensation attempts                : 0
% 3.59/3.82  # Condensation successes               : 0
% 3.59/3.82  # Termbank termtop insertions          : 4452546
% 3.59/3.83  
% 3.59/3.83  # -------------------------------------------------
% 3.59/3.83  # User time                : 3.360 s
% 3.59/3.83  # System time              : 0.093 s
% 3.59/3.83  # Total time               : 3.453 s
% 3.59/3.83  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
