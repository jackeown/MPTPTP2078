%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:01 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 335 expanded)
%              Number of clauses        :   39 ( 154 expanded)
%              Number of leaves         :   10 (  85 expanded)
%              Depth                    :   13
%              Number of atoms          :  184 (1034 expanded)
%              Number of equality atoms :   89 ( 544 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t73_zfmisc_1])).

fof(c_0_11,negated_conjecture,
    ( ( k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_xboole_0
      | ~ r2_hidden(esk4_0,esk6_0)
      | ~ r2_hidden(esk5_0,esk6_0) )
    & ( r2_hidden(esk4_0,esk6_0)
      | k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_xboole_0 )
    & ( r2_hidden(esk5_0,esk6_0)
      | k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_12,plain,(
    ! [X56,X57] : k1_enumset1(X56,X56,X57) = k2_tarski(X56,X57) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X58,X59,X60] : k2_enumset1(X58,X58,X59,X60) = k1_enumset1(X58,X59,X60) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X23,X24] :
      ( ( k4_xboole_0(X23,X24) != k1_xboole_0
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | k4_xboole_0(X23,X24) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X42,X43,X44,X45,X46,X47,X48,X49,X50,X51] :
      ( ( ~ r2_hidden(X46,X45)
        | X46 = X42
        | X46 = X43
        | X46 = X44
        | X45 != k1_enumset1(X42,X43,X44) )
      & ( X47 != X42
        | r2_hidden(X47,X45)
        | X45 != k1_enumset1(X42,X43,X44) )
      & ( X47 != X43
        | r2_hidden(X47,X45)
        | X45 != k1_enumset1(X42,X43,X44) )
      & ( X47 != X44
        | r2_hidden(X47,X45)
        | X45 != k1_enumset1(X42,X43,X44) )
      & ( esk3_4(X48,X49,X50,X51) != X48
        | ~ r2_hidden(esk3_4(X48,X49,X50,X51),X51)
        | X51 = k1_enumset1(X48,X49,X50) )
      & ( esk3_4(X48,X49,X50,X51) != X49
        | ~ r2_hidden(esk3_4(X48,X49,X50,X51),X51)
        | X51 = k1_enumset1(X48,X49,X50) )
      & ( esk3_4(X48,X49,X50,X51) != X50
        | ~ r2_hidden(esk3_4(X48,X49,X50,X51),X51)
        | X51 = k1_enumset1(X48,X49,X50) )
      & ( r2_hidden(esk3_4(X48,X49,X50,X51),X51)
        | esk3_4(X48,X49,X50,X51) = X48
        | esk3_4(X48,X49,X50,X51) = X49
        | esk3_4(X48,X49,X50,X51) = X50
        | X51 = k1_enumset1(X48,X49,X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_19,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0) = k1_xboole_0
    | r2_hidden(esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[c_0_22,c_0_17])).

fof(c_0_26,plain,(
    ! [X63,X64] :
      ( ( k4_xboole_0(X63,k1_tarski(X64)) != X63
        | ~ r2_hidden(X64,X63) )
      & ( r2_hidden(X64,X63)
        | k4_xboole_0(X63,k1_tarski(X64)) = X63 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_27,plain,(
    ! [X55] : k2_tarski(X55,X55) = k1_tarski(X55) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_xboole_0
    | ~ r2_hidden(esk4_0,esk6_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X35] : k4_xboole_0(k1_xboole_0,X35) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0) = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_16]),c_0_17])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0) != k1_xboole_0
    | ~ r2_hidden(esk4_0,esk6_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_16]),c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_39,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( r2_hidden(X15,X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X12)
        | r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk2_3(X17,X18,X19),X19)
        | ~ r2_hidden(esk2_3(X17,X18,X19),X17)
        | r2_hidden(esk2_3(X17,X18,X19),X18)
        | X19 = k4_xboole_0(X17,X18) )
      & ( r2_hidden(esk2_3(X17,X18,X19),X17)
        | r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk2_3(X17,X18,X19),X18)
        | r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k4_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_16]),c_0_17])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_35])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_17])).

cnf(c_0_44,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0) != k1_xboole_0
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])])).

cnf(c_0_46,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_42])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).

cnf(c_0_50,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk2_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k1_xboole_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46])]),c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k2_enumset1(X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk2_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k1_xboole_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])])).

cnf(c_0_55,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_56,negated_conjecture,
    ( esk2_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k1_xboole_0) = esk5_0
    | esk2_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k1_xboole_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_52])])).

cnf(c_0_58,negated_conjecture,
    ( esk2_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k1_xboole_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_52])]),c_0_57]),c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_58]),c_0_38])]),c_0_57]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.64/1.89  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 1.64/1.89  # and selection function SelectNegativeLiterals.
% 1.64/1.89  #
% 1.64/1.89  # Preprocessing time       : 0.029 s
% 1.64/1.89  # Presaturation interreduction done
% 1.64/1.89  
% 1.64/1.89  # Proof found!
% 1.64/1.89  # SZS status Theorem
% 1.64/1.89  # SZS output start CNFRefutation
% 1.64/1.89  fof(t73_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 1.64/1.89  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.64/1.89  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.64/1.89  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.64/1.89  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.64/1.89  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.64/1.89  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.64/1.89  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.64/1.89  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.64/1.89  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.64/1.89  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3)))), inference(assume_negation,[status(cth)],[t73_zfmisc_1])).
% 1.64/1.89  fof(c_0_11, negated_conjecture, ((k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_xboole_0|(~r2_hidden(esk4_0,esk6_0)|~r2_hidden(esk5_0,esk6_0)))&((r2_hidden(esk4_0,esk6_0)|k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_xboole_0)&(r2_hidden(esk5_0,esk6_0)|k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 1.64/1.89  fof(c_0_12, plain, ![X56, X57]:k1_enumset1(X56,X56,X57)=k2_tarski(X56,X57), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.64/1.89  fof(c_0_13, plain, ![X58, X59, X60]:k2_enumset1(X58,X58,X59,X60)=k1_enumset1(X58,X59,X60), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.64/1.89  fof(c_0_14, plain, ![X23, X24]:((k4_xboole_0(X23,X24)!=k1_xboole_0|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|k4_xboole_0(X23,X24)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 1.64/1.89  cnf(c_0_15, negated_conjecture, (r2_hidden(esk4_0,esk6_0)|k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.64/1.89  cnf(c_0_16, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.64/1.89  cnf(c_0_17, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.64/1.89  fof(c_0_18, plain, ![X42, X43, X44, X45, X46, X47, X48, X49, X50, X51]:(((~r2_hidden(X46,X45)|(X46=X42|X46=X43|X46=X44)|X45!=k1_enumset1(X42,X43,X44))&(((X47!=X42|r2_hidden(X47,X45)|X45!=k1_enumset1(X42,X43,X44))&(X47!=X43|r2_hidden(X47,X45)|X45!=k1_enumset1(X42,X43,X44)))&(X47!=X44|r2_hidden(X47,X45)|X45!=k1_enumset1(X42,X43,X44))))&((((esk3_4(X48,X49,X50,X51)!=X48|~r2_hidden(esk3_4(X48,X49,X50,X51),X51)|X51=k1_enumset1(X48,X49,X50))&(esk3_4(X48,X49,X50,X51)!=X49|~r2_hidden(esk3_4(X48,X49,X50,X51),X51)|X51=k1_enumset1(X48,X49,X50)))&(esk3_4(X48,X49,X50,X51)!=X50|~r2_hidden(esk3_4(X48,X49,X50,X51),X51)|X51=k1_enumset1(X48,X49,X50)))&(r2_hidden(esk3_4(X48,X49,X50,X51),X51)|(esk3_4(X48,X49,X50,X51)=X48|esk3_4(X48,X49,X50,X51)=X49|esk3_4(X48,X49,X50,X51)=X50)|X51=k1_enumset1(X48,X49,X50)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 1.64/1.89  fof(c_0_19, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.64/1.89  cnf(c_0_20, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.64/1.89  cnf(c_0_21, negated_conjecture, (k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)=k1_xboole_0|r2_hidden(esk4_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 1.64/1.89  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.64/1.89  cnf(c_0_23, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.64/1.89  cnf(c_0_24, negated_conjecture, (r2_hidden(esk4_0,esk6_0)|r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 1.64/1.89  cnf(c_0_25, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X2,X5)), inference(rw,[status(thm)],[c_0_22, c_0_17])).
% 1.64/1.89  fof(c_0_26, plain, ![X63, X64]:((k4_xboole_0(X63,k1_tarski(X64))!=X63|~r2_hidden(X64,X63))&(r2_hidden(X64,X63)|k4_xboole_0(X63,k1_tarski(X64))=X63)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 1.64/1.89  fof(c_0_27, plain, ![X55]:k2_tarski(X55,X55)=k1_tarski(X55), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.64/1.89  cnf(c_0_28, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.64/1.89  cnf(c_0_29, negated_conjecture, (k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_xboole_0|~r2_hidden(esk4_0,esk6_0)|~r2_hidden(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.64/1.89  cnf(c_0_30, negated_conjecture, (r2_hidden(esk4_0,esk6_0)|r2_hidden(X1,esk6_0)|~r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 1.64/1.89  cnf(c_0_31, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X1,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])])).
% 1.64/1.89  cnf(c_0_32, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.64/1.89  cnf(c_0_33, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.64/1.89  fof(c_0_34, plain, ![X35]:k4_xboole_0(k1_xboole_0,X35)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 1.64/1.89  cnf(c_0_35, negated_conjecture, (k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_16]), c_0_17])).
% 1.64/1.89  cnf(c_0_36, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.64/1.89  cnf(c_0_37, negated_conjecture, (k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)!=k1_xboole_0|~r2_hidden(esk4_0,esk6_0)|~r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_16]), c_0_17])).
% 1.64/1.89  cnf(c_0_38, negated_conjecture, (r2_hidden(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 1.64/1.89  fof(c_0_39, plain, ![X12, X13, X14, X15, X16, X17, X18, X19]:((((r2_hidden(X15,X12)|~r2_hidden(X15,X14)|X14!=k4_xboole_0(X12,X13))&(~r2_hidden(X15,X13)|~r2_hidden(X15,X14)|X14!=k4_xboole_0(X12,X13)))&(~r2_hidden(X16,X12)|r2_hidden(X16,X13)|r2_hidden(X16,X14)|X14!=k4_xboole_0(X12,X13)))&((~r2_hidden(esk2_3(X17,X18,X19),X19)|(~r2_hidden(esk2_3(X17,X18,X19),X17)|r2_hidden(esk2_3(X17,X18,X19),X18))|X19=k4_xboole_0(X17,X18))&((r2_hidden(esk2_3(X17,X18,X19),X17)|r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k4_xboole_0(X17,X18))&(~r2_hidden(esk2_3(X17,X18,X19),X18)|r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k4_xboole_0(X17,X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 1.64/1.89  cnf(c_0_40, plain, (k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_16]), c_0_17])).
% 1.64/1.89  cnf(c_0_41, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.64/1.89  cnf(c_0_42, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|r1_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_20, c_0_35])).
% 1.64/1.89  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X5,X2)), inference(rw,[status(thm)],[c_0_36, c_0_17])).
% 1.64/1.89  cnf(c_0_44, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.64/1.89  cnf(c_0_45, negated_conjecture, (k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)!=k1_xboole_0|~r2_hidden(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38])])).
% 1.64/1.89  cnf(c_0_46, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.64/1.89  cnf(c_0_47, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.64/1.89  cnf(c_0_48, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|r2_hidden(X1,esk6_0)|~r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_23, c_0_42])).
% 1.64/1.89  cnf(c_0_49, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).
% 1.64/1.89  cnf(c_0_50, plain, (X1=X5|X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_44, c_0_17])).
% 1.64/1.89  cnf(c_0_51, negated_conjecture, (r2_hidden(esk2_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k1_xboole_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))|~r2_hidden(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46])]), c_0_47])).
% 1.64/1.89  cnf(c_0_52, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.64/1.89  cnf(c_0_53, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k2_enumset1(X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_50])).
% 1.64/1.89  cnf(c_0_54, negated_conjecture, (r2_hidden(esk2_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k1_xboole_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52])])).
% 1.64/1.89  cnf(c_0_55, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.64/1.89  cnf(c_0_56, negated_conjecture, (esk2_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k1_xboole_0)=esk5_0|esk2_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k1_xboole_0)=esk4_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 1.64/1.89  cnf(c_0_57, negated_conjecture, (k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_52])])).
% 1.64/1.89  cnf(c_0_58, negated_conjecture, (esk2_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k1_xboole_0)=esk4_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_52])]), c_0_57]), c_0_47])).
% 1.64/1.89  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_58]), c_0_38])]), c_0_57]), c_0_47]), ['proof']).
% 1.64/1.89  # SZS output end CNFRefutation
% 1.64/1.89  # Proof object total steps             : 60
% 1.64/1.89  # Proof object clause steps            : 39
% 1.64/1.89  # Proof object formula steps           : 21
% 1.64/1.89  # Proof object conjectures             : 22
% 1.64/1.89  # Proof object clause conjectures      : 19
% 1.64/1.89  # Proof object formula conjectures     : 3
% 1.64/1.89  # Proof object initial clauses used    : 15
% 1.64/1.89  # Proof object initial formulas used   : 10
% 1.64/1.89  # Proof object generating inferences   : 11
% 1.64/1.89  # Proof object simplifying inferences  : 33
% 1.64/1.89  # Training examples: 0 positive, 0 negative
% 1.64/1.89  # Parsed axioms                        : 21
% 1.64/1.89  # Removed by relevancy pruning/SinE    : 0
% 1.64/1.89  # Initial clauses                      : 43
% 1.64/1.89  # Removed in clause preprocessing      : 3
% 1.64/1.89  # Initial clauses in saturation        : 40
% 1.64/1.89  # Processed clauses                    : 4214
% 1.64/1.89  # ...of these trivial                  : 107
% 1.64/1.89  # ...subsumed                          : 3467
% 1.64/1.89  # ...remaining for further processing  : 640
% 1.64/1.89  # Other redundant clauses eliminated   : 1630
% 1.64/1.89  # Clauses deleted for lack of memory   : 0
% 1.64/1.89  # Backward-subsumed                    : 4
% 1.64/1.89  # Backward-rewritten                   : 69
% 1.64/1.89  # Generated clauses                    : 80270
% 1.64/1.89  # ...of the previous two non-trivial   : 70420
% 1.64/1.89  # Contextual simplify-reflections      : 4
% 1.64/1.89  # Paramodulations                      : 78395
% 1.64/1.89  # Factorizations                       : 248
% 1.64/1.89  # Equation resolutions                 : 1630
% 1.64/1.89  # Propositional unsat checks           : 0
% 1.64/1.89  #    Propositional check models        : 0
% 1.64/1.89  #    Propositional check unsatisfiable : 0
% 1.64/1.89  #    Propositional clauses             : 0
% 1.64/1.89  #    Propositional clauses after purity: 0
% 1.64/1.89  #    Propositional unsat core size     : 0
% 1.64/1.89  #    Propositional preprocessing time  : 0.000
% 1.64/1.89  #    Propositional encoding time       : 0.000
% 1.64/1.89  #    Propositional solver time         : 0.000
% 1.64/1.89  #    Success case prop preproc time    : 0.000
% 1.64/1.89  #    Success case prop encoding time   : 0.000
% 1.64/1.89  #    Success case prop solver time     : 0.000
% 1.64/1.89  # Current number of processed clauses  : 519
% 1.64/1.89  #    Positive orientable unit clauses  : 91
% 1.64/1.89  #    Positive unorientable unit clauses: 1
% 1.64/1.89  #    Negative unit clauses             : 36
% 1.64/1.89  #    Non-unit-clauses                  : 391
% 1.64/1.89  # Current number of unprocessed clauses: 66058
% 1.64/1.89  # ...number of literals in the above   : 330838
% 1.64/1.89  # Current number of archived formulas  : 0
% 1.64/1.89  # Current number of archived clauses   : 115
% 1.64/1.89  # Clause-clause subsumption calls (NU) : 42087
% 1.64/1.89  # Rec. Clause-clause subsumption calls : 27228
% 1.64/1.89  # Non-unit clause-clause subsumptions  : 1542
% 1.64/1.89  # Unit Clause-clause subsumption calls : 1550
% 1.64/1.89  # Rewrite failures with RHS unbound    : 0
% 1.64/1.89  # BW rewrite match attempts            : 147
% 1.64/1.89  # BW rewrite match successes           : 39
% 1.64/1.89  # Condensation attempts                : 0
% 1.64/1.89  # Condensation successes               : 0
% 1.64/1.89  # Termbank termtop insertions          : 1463791
% 1.64/1.89  
% 1.64/1.89  # -------------------------------------------------
% 1.64/1.89  # User time                : 1.490 s
% 1.64/1.89  # System time              : 0.058 s
% 1.64/1.89  # Total time               : 1.548 s
% 1.64/1.89  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
