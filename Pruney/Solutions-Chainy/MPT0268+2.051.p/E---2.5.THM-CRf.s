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
% DateTime   : Thu Dec  3 10:42:24 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 483 expanded)
%              Number of clauses        :   39 ( 226 expanded)
%              Number of leaves         :   12 ( 126 expanded)
%              Depth                    :   14
%              Number of atoms          :  175 (1282 expanded)
%              Number of equality atoms :   83 ( 691 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

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

fof(t65_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_12,plain,(
    ! [X26,X27] : r1_xboole_0(k4_xboole_0(X26,X27),X27) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_13,plain,(
    ! [X23,X24] : k4_xboole_0(X23,X24) = k5_xboole_0(X23,k3_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_14,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_xboole_0(X15,X16) )
      & ( r2_hidden(esk2_2(X15,X16),X16)
        | r1_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_15,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X25] : k4_xboole_0(X25,k1_xboole_0) = X25 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_18,plain,(
    ! [X28,X29,X30,X31,X32,X33,X34,X35,X36,X37] :
      ( ( ~ r2_hidden(X32,X31)
        | X32 = X28
        | X32 = X29
        | X32 = X30
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X28
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X29
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X30
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( esk4_4(X34,X35,X36,X37) != X34
        | ~ r2_hidden(esk4_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( esk4_4(X34,X35,X36,X37) != X35
        | ~ r2_hidden(esk4_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( esk4_4(X34,X35,X36,X37) != X36
        | ~ r2_hidden(esk4_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( r2_hidden(esk4_4(X34,X35,X36,X37),X37)
        | esk4_4(X34,X35,X36,X37) = X34
        | esk4_4(X34,X35,X36,X37) = X35
        | esk4_4(X34,X35,X36,X37) = X36
        | X37 = k1_enumset1(X34,X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_19,plain,(
    ! [X42,X43,X44] : k2_enumset1(X42,X42,X43,X44) = k1_enumset1(X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X45,X46,X47,X48] : k3_enumset1(X45,X45,X46,X47,X48) = k2_enumset1(X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(X1,k1_tarski(X2)) = X1
      <=> ~ r2_hidden(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t65_zfmisc_1])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,negated_conjecture,
    ( ( k4_xboole_0(esk5_0,k1_tarski(esk6_0)) != esk5_0
      | r2_hidden(esk6_0,esk5_0) )
    & ( k4_xboole_0(esk5_0,k1_tarski(esk6_0)) = esk5_0
      | ~ r2_hidden(esk6_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

fof(c_0_29,plain,(
    ! [X39] : k2_tarski(X39,X39) = k1_tarski(X39) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_30,plain,(
    ! [X40,X41] : k1_enumset1(X40,X40,X41) = k2_tarski(X40,X41) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_24,c_0_16])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0)
    | k4_xboole_0(esk5_0,k1_tarski(esk6_0)) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,plain,(
    ! [X21] :
      ( X21 = k1_xboole_0
      | r2_hidden(esk3_1(X21),X21) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_38,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | ~ r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k3_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k3_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k3_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0)
    | k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_16]),c_0_26]),c_0_27])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))
    | r2_hidden(esk6_0,esk5_0)
    | k5_xboole_0(esk5_0,k1_xboole_0) != esk5_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,k1_xboole_0,X2),X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_43]),c_0_44])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_26]),c_0_27])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))
    | r2_hidden(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_44])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_54,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))
    | r2_hidden(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(esk5_0,k1_tarski(esk6_0)) = esk5_0
    | ~ r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),esk5_0)
    | r2_hidden(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) = esk6_0
    | r2_hidden(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) = esk5_0
    | ~ r2_hidden(esk6_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_35]),c_0_36]),c_0_16]),c_0_26]),c_0_27])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(X1,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_40]),c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n009.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 20:01:11 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.31  # Version: 2.5pre002
% 0.16/0.31  # No SInE strategy applied
% 0.16/0.31  # Trying AutoSched0 for 299 seconds
% 0.78/0.94  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.78/0.94  # and selection function SelectNegativeLiterals.
% 0.78/0.94  #
% 0.78/0.94  # Preprocessing time       : 0.028 s
% 0.78/0.94  # Presaturation interreduction done
% 0.78/0.94  
% 0.78/0.94  # Proof found!
% 0.78/0.94  # SZS status Theorem
% 0.78/0.94  # SZS output start CNFRefutation
% 0.78/0.94  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.78/0.94  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.78/0.94  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.78/0.94  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.78/0.94  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.78/0.94  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.78/0.94  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.78/0.94  fof(t65_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.78/0.94  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.78/0.94  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.78/0.94  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.78/0.94  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.78/0.94  fof(c_0_12, plain, ![X26, X27]:r1_xboole_0(k4_xboole_0(X26,X27),X27), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.78/0.94  fof(c_0_13, plain, ![X23, X24]:k4_xboole_0(X23,X24)=k5_xboole_0(X23,k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.78/0.94  fof(c_0_14, plain, ![X15, X16, X18, X19, X20]:(((r2_hidden(esk2_2(X15,X16),X15)|r1_xboole_0(X15,X16))&(r2_hidden(esk2_2(X15,X16),X16)|r1_xboole_0(X15,X16)))&(~r2_hidden(X20,X18)|~r2_hidden(X20,X19)|~r1_xboole_0(X18,X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.78/0.94  cnf(c_0_15, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.78/0.94  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.78/0.94  fof(c_0_17, plain, ![X25]:k4_xboole_0(X25,k1_xboole_0)=X25, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.78/0.94  fof(c_0_18, plain, ![X28, X29, X30, X31, X32, X33, X34, X35, X36, X37]:(((~r2_hidden(X32,X31)|(X32=X28|X32=X29|X32=X30)|X31!=k1_enumset1(X28,X29,X30))&(((X33!=X28|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30))&(X33!=X29|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30)))&(X33!=X30|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30))))&((((esk4_4(X34,X35,X36,X37)!=X34|~r2_hidden(esk4_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36))&(esk4_4(X34,X35,X36,X37)!=X35|~r2_hidden(esk4_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36)))&(esk4_4(X34,X35,X36,X37)!=X36|~r2_hidden(esk4_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36)))&(r2_hidden(esk4_4(X34,X35,X36,X37),X37)|(esk4_4(X34,X35,X36,X37)=X34|esk4_4(X34,X35,X36,X37)=X35|esk4_4(X34,X35,X36,X37)=X36)|X37=k1_enumset1(X34,X35,X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.78/0.94  fof(c_0_19, plain, ![X42, X43, X44]:k2_enumset1(X42,X42,X43,X44)=k1_enumset1(X42,X43,X44), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.78/0.94  fof(c_0_20, plain, ![X45, X46, X47, X48]:k3_enumset1(X45,X45,X46,X47,X48)=k2_enumset1(X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.78/0.94  fof(c_0_21, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1)))), inference(assume_negation,[status(cth)],[t65_zfmisc_1])).
% 0.78/0.94  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.78/0.94  cnf(c_0_23, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.78/0.94  cnf(c_0_24, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.78/0.94  cnf(c_0_25, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.78/0.94  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.78/0.94  cnf(c_0_27, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.78/0.94  fof(c_0_28, negated_conjecture, ((k4_xboole_0(esk5_0,k1_tarski(esk6_0))!=esk5_0|r2_hidden(esk6_0,esk5_0))&(k4_xboole_0(esk5_0,k1_tarski(esk6_0))=esk5_0|~r2_hidden(esk6_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.78/0.94  fof(c_0_29, plain, ![X39]:k2_tarski(X39,X39)=k1_tarski(X39), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.78/0.94  fof(c_0_30, plain, ![X40, X41]:k1_enumset1(X40,X40,X41)=k2_tarski(X40,X41), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.78/0.94  cnf(c_0_31, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.78/0.94  cnf(c_0_32, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_24, c_0_16])).
% 0.78/0.94  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.78/0.94  cnf(c_0_34, negated_conjecture, (r2_hidden(esk6_0,esk5_0)|k4_xboole_0(esk5_0,k1_tarski(esk6_0))!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.78/0.94  cnf(c_0_35, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.78/0.94  cnf(c_0_36, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.78/0.94  fof(c_0_37, plain, ![X21]:(X21=k1_xboole_0|r2_hidden(esk3_1(X21),X21)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.78/0.94  fof(c_0_38, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7))&(r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k3_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k3_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))&(r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.78/0.94  cnf(c_0_39, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.78/0.94  cnf(c_0_40, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])])).
% 0.78/0.94  cnf(c_0_41, negated_conjecture, (r2_hidden(esk6_0,esk5_0)|k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_16]), c_0_26]), c_0_27])).
% 0.78/0.94  cnf(c_0_42, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.78/0.94  cnf(c_0_43, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.78/0.94  cnf(c_0_44, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.78/0.94  cnf(c_0_45, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.78/0.94  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.78/0.94  cnf(c_0_47, negated_conjecture, (r2_hidden(esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))|r2_hidden(esk6_0,esk5_0)|k5_xboole_0(esk5_0,k1_xboole_0)!=esk5_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.78/0.94  cnf(c_0_48, plain, (k5_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,k1_xboole_0,X2),X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_43]), c_0_44])).
% 0.78/0.94  cnf(c_0_49, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.78/0.94  cnf(c_0_50, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_26]), c_0_27])).
% 0.78/0.94  cnf(c_0_51, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_46])).
% 0.78/0.94  cnf(c_0_52, negated_conjecture, (r2_hidden(esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))|r2_hidden(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_44])).
% 0.78/0.94  cnf(c_0_53, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_49])).
% 0.78/0.94  cnf(c_0_54, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_50])).
% 0.78/0.94  cnf(c_0_55, negated_conjecture, (r2_hidden(esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))|r2_hidden(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.78/0.94  cnf(c_0_56, negated_conjecture, (k4_xboole_0(esk5_0,k1_tarski(esk6_0))=esk5_0|~r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.78/0.94  cnf(c_0_57, negated_conjecture, (r2_hidden(esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),esk5_0)|r2_hidden(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_53, c_0_52])).
% 0.78/0.94  cnf(c_0_58, negated_conjecture, (esk3_1(k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))=esk6_0|r2_hidden(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.78/0.94  cnf(c_0_59, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))=esk5_0|~r2_hidden(esk6_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_35]), c_0_36]), c_0_16]), c_0_26]), c_0_27])).
% 0.78/0.94  cnf(c_0_60, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.78/0.94  cnf(c_0_61, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])])).
% 0.78/0.94  cnf(c_0_62, negated_conjecture, (~r2_hidden(X1,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_31, c_0_61])).
% 0.78/0.94  cnf(c_0_63, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_40]), c_0_60])]), ['proof']).
% 0.78/0.94  # SZS output end CNFRefutation
% 0.78/0.94  # Proof object total steps             : 64
% 0.78/0.94  # Proof object clause steps            : 39
% 0.78/0.94  # Proof object formula steps           : 25
% 0.78/0.94  # Proof object conjectures             : 16
% 0.78/0.94  # Proof object clause conjectures      : 13
% 0.78/0.94  # Proof object formula conjectures     : 3
% 0.78/0.94  # Proof object initial clauses used    : 16
% 0.78/0.94  # Proof object initial formulas used   : 12
% 0.78/0.94  # Proof object generating inferences   : 12
% 0.78/0.94  # Proof object simplifying inferences  : 27
% 0.78/0.94  # Training examples: 0 positive, 0 negative
% 0.78/0.94  # Parsed axioms                        : 13
% 0.78/0.94  # Removed by relevancy pruning/SinE    : 0
% 0.78/0.94  # Initial clauses                      : 28
% 0.78/0.94  # Removed in clause preprocessing      : 5
% 0.78/0.94  # Initial clauses in saturation        : 23
% 0.78/0.94  # Processed clauses                    : 1334
% 0.78/0.94  # ...of these trivial                  : 87
% 0.78/0.94  # ...subsumed                          : 488
% 0.78/0.94  # ...remaining for further processing  : 759
% 0.78/0.94  # Other redundant clauses eliminated   : 78
% 0.78/0.94  # Clauses deleted for lack of memory   : 0
% 0.78/0.94  # Backward-subsumed                    : 4
% 0.78/0.94  # Backward-rewritten                   : 34
% 0.78/0.94  # Generated clauses                    : 59561
% 0.78/0.94  # ...of the previous two non-trivial   : 45680
% 0.78/0.94  # Contextual simplify-reflections      : 0
% 0.78/0.94  # Paramodulations                      : 59474
% 0.78/0.94  # Factorizations                       : 12
% 0.78/0.94  # Equation resolutions                 : 78
% 0.78/0.94  # Propositional unsat checks           : 0
% 0.78/0.94  #    Propositional check models        : 0
% 0.78/0.94  #    Propositional check unsatisfiable : 0
% 0.78/0.94  #    Propositional clauses             : 0
% 0.78/0.94  #    Propositional clauses after purity: 0
% 0.78/0.94  #    Propositional unsat core size     : 0
% 0.78/0.94  #    Propositional preprocessing time  : 0.000
% 0.78/0.94  #    Propositional encoding time       : 0.000
% 0.78/0.94  #    Propositional solver time         : 0.000
% 0.78/0.94  #    Success case prop preproc time    : 0.000
% 0.78/0.94  #    Success case prop encoding time   : 0.000
% 0.78/0.94  #    Success case prop solver time     : 0.000
% 0.78/0.94  # Current number of processed clauses  : 691
% 0.78/0.94  #    Positive orientable unit clauses  : 343
% 0.78/0.94  #    Positive unorientable unit clauses: 0
% 0.78/0.94  #    Negative unit clauses             : 1
% 0.78/0.94  #    Non-unit-clauses                  : 347
% 0.78/0.94  # Current number of unprocessed clauses: 44273
% 0.78/0.94  # ...number of literals in the above   : 140963
% 0.78/0.94  # Current number of archived formulas  : 0
% 0.78/0.94  # Current number of archived clauses   : 66
% 0.78/0.94  # Clause-clause subsumption calls (NU) : 20077
% 0.78/0.94  # Rec. Clause-clause subsumption calls : 19311
% 0.78/0.94  # Non-unit clause-clause subsumptions  : 123
% 0.78/0.94  # Unit Clause-clause subsumption calls : 160
% 0.78/0.94  # Rewrite failures with RHS unbound    : 0
% 0.78/0.94  # BW rewrite match attempts            : 4755
% 0.78/0.94  # BW rewrite match successes           : 5
% 0.78/0.94  # Condensation attempts                : 0
% 0.78/0.94  # Condensation successes               : 0
% 0.78/0.94  # Termbank termtop insertions          : 1105701
% 0.78/0.94  
% 0.78/0.94  # -------------------------------------------------
% 0.78/0.94  # User time                : 0.607 s
% 0.78/0.94  # System time              : 0.026 s
% 0.78/0.94  # Total time               : 0.633 s
% 0.78/0.94  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
