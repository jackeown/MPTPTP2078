%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:02 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 138 expanded)
%              Number of clauses        :   48 (  67 expanded)
%              Number of leaves         :   11 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  218 ( 516 expanded)
%              Number of equality atoms :   27 (  76 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

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

fof(l33_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t75_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_xboole_0(k3_xboole_0(X1,X2),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_11,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( r2_hidden(X23,X20)
        | ~ r2_hidden(X23,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X20)
        | r2_hidden(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk3_3(X25,X26,X27),X27)
        | ~ r2_hidden(esk3_3(X25,X26,X27),X25)
        | r2_hidden(esk3_3(X25,X26,X27),X26)
        | X27 = k4_xboole_0(X25,X26) )
      & ( r2_hidden(esk3_3(X25,X26,X27),X25)
        | r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k4_xboole_0(X25,X26) )
      & ( ~ r2_hidden(esk3_3(X25,X26,X27),X26)
        | r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k4_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_13,plain,(
    ! [X51,X52] :
      ( ( ~ r1_xboole_0(X51,X52)
        | k4_xboole_0(X51,X52) = X51 )
      & ( k4_xboole_0(X51,X52) != X51
        | r1_xboole_0(X51,X52) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk6_0,esk7_0),k1_tarski(esk9_0))
    & r2_hidden(esk9_0,esk8_0)
    & r1_xboole_0(esk8_0,esk7_0)
    & ~ r1_xboole_0(k2_xboole_0(esk6_0,esk8_0),esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_18,plain,(
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

cnf(c_0_19,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X31,X32,X34,X35,X36] :
      ( ( r2_hidden(esk4_2(X31,X32),X31)
        | r1_xboole_0(X31,X32) )
      & ( r2_hidden(esk4_2(X31,X32),X32)
        | r1_xboole_0(X31,X32) )
      & ( ~ r2_hidden(X36,X34)
        | ~ r2_hidden(X36,X35)
        | ~ r1_xboole_0(X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X53,X54] :
      ( ( k4_xboole_0(k1_tarski(X53),X54) != k1_tarski(X53)
        | ~ r2_hidden(X53,X54) )
      & ( r2_hidden(X53,X54)
        | k4_xboole_0(k1_tarski(X53),X54) = k1_tarski(X53) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X29,X30] :
      ( ~ r1_xboole_0(X29,X30)
      | r1_xboole_0(X30,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(esk8_0,X1)
    | ~ r2_hidden(esk4_2(esk8_0,X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | r2_hidden(esk4_2(X1,k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_33,plain,(
    ! [X49,X50] :
      ( r1_xboole_0(X49,X50)
      | ~ r1_xboole_0(k3_xboole_0(X49,X50),X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r1_xboole_0(k1_tarski(X1),X2)
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r1_xboole_0(esk8_0,k3_xboole_0(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,k1_tarski(X2))
    | r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_39,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(X1,k3_xboole_0(esk7_0,X2))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_36])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,k1_tarski(X2))
    | r2_hidden(X2,k3_xboole_0(X1,k1_tarski(X2))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_45,plain,(
    ! [X37,X38,X40,X41,X42] :
      ( ( r1_xboole_0(X37,X38)
        | r2_hidden(esk5_2(X37,X38),k3_xboole_0(X37,X38)) )
      & ( ~ r2_hidden(X42,k3_xboole_0(X40,X41))
        | ~ r1_xboole_0(X40,X41) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_46,negated_conjecture,
    ( r1_xboole_0(esk7_0,k1_tarski(X1))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk6_0,esk7_0),k1_tarski(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) != k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(esk4_2(X1,k4_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_27])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk5_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(X1,k1_tarski(X2))
    | ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_2(k3_xboole_0(esk6_0,esk7_0),X1),k1_tarski(esk9_0))
    | r1_tarski(k3_xboole_0(esk6_0,esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2)
    | r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_43])).

fof(c_0_57,plain,(
    ! [X46,X47,X48] :
      ( ( r1_xboole_0(X46,k2_xboole_0(X47,X48))
        | ~ r1_xboole_0(X46,X47)
        | ~ r1_xboole_0(X46,X48) )
      & ( r1_xboole_0(X46,X47)
        | ~ r1_xboole_0(X46,k2_xboole_0(X47,X48)) )
      & ( r1_xboole_0(X46,X48)
        | ~ r1_xboole_0(X46,k2_xboole_0(X47,X48)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_58,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_16])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_25])).

cnf(c_0_60,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk5_2(X1,X2),X3)
    | ~ r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk6_0,esk7_0),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])]),c_0_56])).

cnf(c_0_62,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk7_0)
    | r2_hidden(esk5_2(esk6_0,esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk6_0,esk8_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_66,plain,
    ( r1_xboole_0(k2_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( r1_xboole_0(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_20])).

cnf(c_0_68,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_xboole_0(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_68]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:23:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05AN
% 0.19/0.42  # and selection function PSelectComplexExceptUniqMaxPosHorn.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.028 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.42  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.19/0.42  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.19/0.42  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.42  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.42  fof(l33_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 0.19/0.42  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.42  fof(t75_xboole_1, axiom, ![X1, X2]:~((~(r1_xboole_0(X1,X2))&r1_xboole_0(k3_xboole_0(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 0.19/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.42  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.42  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.19/0.42  fof(c_0_11, plain, ![X20, X21, X22, X23, X24, X25, X26, X27]:((((r2_hidden(X23,X20)|~r2_hidden(X23,X22)|X22!=k4_xboole_0(X20,X21))&(~r2_hidden(X23,X21)|~r2_hidden(X23,X22)|X22!=k4_xboole_0(X20,X21)))&(~r2_hidden(X24,X20)|r2_hidden(X24,X21)|r2_hidden(X24,X22)|X22!=k4_xboole_0(X20,X21)))&((~r2_hidden(esk3_3(X25,X26,X27),X27)|(~r2_hidden(esk3_3(X25,X26,X27),X25)|r2_hidden(esk3_3(X25,X26,X27),X26))|X27=k4_xboole_0(X25,X26))&((r2_hidden(esk3_3(X25,X26,X27),X25)|r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k4_xboole_0(X25,X26))&(~r2_hidden(esk3_3(X25,X26,X27),X26)|r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k4_xboole_0(X25,X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.42  cnf(c_0_12, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.42  fof(c_0_13, plain, ![X51, X52]:((~r1_xboole_0(X51,X52)|k4_xboole_0(X51,X52)=X51)&(k4_xboole_0(X51,X52)!=X51|r1_xboole_0(X51,X52))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.19/0.42  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.19/0.42  cnf(c_0_15, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_12])).
% 0.19/0.42  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  fof(c_0_17, negated_conjecture, (((r1_tarski(k3_xboole_0(esk6_0,esk7_0),k1_tarski(esk9_0))&r2_hidden(esk9_0,esk8_0))&r1_xboole_0(esk8_0,esk7_0))&~r1_xboole_0(k2_xboole_0(esk6_0,esk8_0),esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.42  fof(c_0_18, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.42  cnf(c_0_19, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.42  cnf(c_0_20, negated_conjecture, (r1_xboole_0(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  fof(c_0_21, plain, ![X31, X32, X34, X35, X36]:(((r2_hidden(esk4_2(X31,X32),X31)|r1_xboole_0(X31,X32))&(r2_hidden(esk4_2(X31,X32),X32)|r1_xboole_0(X31,X32)))&(~r2_hidden(X36,X34)|~r2_hidden(X36,X35)|~r1_xboole_0(X34,X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.42  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  fof(c_0_23, plain, ![X53, X54]:((k4_xboole_0(k1_tarski(X53),X54)!=k1_tarski(X53)|~r2_hidden(X53,X54))&(r2_hidden(X53,X54)|k4_xboole_0(k1_tarski(X53),X54)=k1_tarski(X53))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).
% 0.19/0.42  cnf(c_0_24, negated_conjecture, (~r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.42  cnf(c_0_25, plain, (r2_hidden(esk4_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  cnf(c_0_26, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_22])).
% 0.19/0.42  cnf(c_0_27, plain, (r2_hidden(esk4_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  fof(c_0_28, plain, ![X29, X30]:(~r1_xboole_0(X29,X30)|r1_xboole_0(X30,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.42  cnf(c_0_29, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_30, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_31, negated_conjecture, (r1_xboole_0(esk8_0,X1)|~r2_hidden(esk4_2(esk8_0,X1),esk7_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.42  cnf(c_0_32, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|r2_hidden(esk4_2(X1,k3_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.42  fof(c_0_33, plain, ![X49, X50]:(r1_xboole_0(X49,X50)|~r1_xboole_0(k3_xboole_0(X49,X50),X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).
% 0.19/0.42  cnf(c_0_34, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.42  cnf(c_0_35, plain, (r1_xboole_0(k1_tarski(X1),X2)|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.42  cnf(c_0_36, negated_conjecture, (r1_xboole_0(esk8_0,k3_xboole_0(esk7_0,X1))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.42  cnf(c_0_37, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k3_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.42  cnf(c_0_38, plain, (r1_xboole_0(X1,k1_tarski(X2))|r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.42  fof(c_0_39, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.42  cnf(c_0_40, negated_conjecture, (~r2_hidden(X1,k3_xboole_0(esk7_0,X2))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_19, c_0_36])).
% 0.19/0.42  cnf(c_0_41, plain, (r1_xboole_0(X1,k1_tarski(X2))|r2_hidden(X2,k3_xboole_0(X1,k1_tarski(X2)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.42  cnf(c_0_42, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.42  cnf(c_0_43, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.42  cnf(c_0_44, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  fof(c_0_45, plain, ![X37, X38, X40, X41, X42]:((r1_xboole_0(X37,X38)|r2_hidden(esk5_2(X37,X38),k3_xboole_0(X37,X38)))&(~r2_hidden(X42,k3_xboole_0(X40,X41))|~r1_xboole_0(X40,X41))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.42  cnf(c_0_46, negated_conjecture, (r1_xboole_0(esk7_0,k1_tarski(X1))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.42  cnf(c_0_47, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.42  cnf(c_0_48, negated_conjecture, (r1_tarski(k3_xboole_0(esk6_0,esk7_0),k1_tarski(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_49, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_44])).
% 0.19/0.42  cnf(c_0_50, plain, (k4_xboole_0(k1_tarski(X1),X2)!=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_51, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r2_hidden(esk4_2(X1,k4_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_15, c_0_27])).
% 0.19/0.42  cnf(c_0_52, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk5_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.42  cnf(c_0_53, negated_conjecture, (~r2_hidden(X1,k1_tarski(X2))|~r2_hidden(X1,esk7_0)|~r2_hidden(X2,esk8_0)), inference(spm,[status(thm)],[c_0_19, c_0_46])).
% 0.19/0.42  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_2(k3_xboole_0(esk6_0,esk7_0),X1),k1_tarski(esk9_0))|r1_tarski(k3_xboole_0(esk6_0,esk7_0),X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.42  cnf(c_0_55, negated_conjecture, (r2_hidden(esk9_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_56, plain, (r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2)|r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_49, c_0_43])).
% 0.19/0.42  fof(c_0_57, plain, ![X46, X47, X48]:((r1_xboole_0(X46,k2_xboole_0(X47,X48))|~r1_xboole_0(X46,X47)|~r1_xboole_0(X46,X48))&((r1_xboole_0(X46,X47)|~r1_xboole_0(X46,k2_xboole_0(X47,X48)))&(r1_xboole_0(X46,X48)|~r1_xboole_0(X46,k2_xboole_0(X47,X48))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.19/0.42  cnf(c_0_58, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_16])).
% 0.19/0.42  cnf(c_0_59, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_51, c_0_25])).
% 0.19/0.42  cnf(c_0_60, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk5_2(X1,X2),X3)|~r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_42, c_0_52])).
% 0.19/0.42  cnf(c_0_61, negated_conjecture, (r1_tarski(k3_xboole_0(esk6_0,esk7_0),X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])]), c_0_56])).
% 0.19/0.42  cnf(c_0_62, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.42  cnf(c_0_63, plain, (~r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X1)))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.42  cnf(c_0_64, negated_conjecture, (r1_xboole_0(esk6_0,esk7_0)|r2_hidden(esk5_2(esk6_0,esk7_0),X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.42  cnf(c_0_65, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk6_0,esk8_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_66, plain, (r1_xboole_0(k2_xboole_0(X1,X2),X3)|~r1_xboole_0(X3,X2)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_34, c_0_62])).
% 0.19/0.42  cnf(c_0_67, negated_conjecture, (r1_xboole_0(esk7_0,esk8_0)), inference(spm,[status(thm)],[c_0_34, c_0_20])).
% 0.19/0.42  cnf(c_0_68, negated_conjecture, (r1_xboole_0(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.42  cnf(c_0_69, negated_conjecture, (~r1_xboole_0(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 0.19/0.42  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_68]), c_0_69]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 71
% 0.19/0.42  # Proof object clause steps            : 48
% 0.19/0.42  # Proof object formula steps           : 23
% 0.19/0.42  # Proof object conjectures             : 20
% 0.19/0.42  # Proof object clause conjectures      : 17
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 19
% 0.19/0.42  # Proof object initial formulas used   : 11
% 0.19/0.42  # Proof object generating inferences   : 26
% 0.19/0.42  # Proof object simplifying inferences  : 9
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 12
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 34
% 0.19/0.42  # Removed in clause preprocessing      : 0
% 0.19/0.42  # Initial clauses in saturation        : 34
% 0.19/0.42  # Processed clauses                    : 750
% 0.19/0.42  # ...of these trivial                  : 50
% 0.19/0.42  # ...subsumed                          : 376
% 0.19/0.42  # ...remaining for further processing  : 324
% 0.19/0.42  # Other redundant clauses eliminated   : 6
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 5
% 0.19/0.42  # Backward-rewritten                   : 6
% 0.19/0.42  # Generated clauses                    : 2887
% 0.19/0.42  # ...of the previous two non-trivial   : 2602
% 0.19/0.42  # Contextual simplify-reflections      : 1
% 0.19/0.42  # Paramodulations                      : 2871
% 0.19/0.42  # Factorizations                       : 10
% 0.19/0.42  # Equation resolutions                 : 6
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 273
% 0.19/0.42  #    Positive orientable unit clauses  : 63
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 19
% 0.19/0.42  #    Non-unit-clauses                  : 191
% 0.19/0.42  # Current number of unprocessed clauses: 1914
% 0.19/0.42  # ...number of literals in the above   : 4915
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 45
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 5209
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 3782
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 248
% 0.19/0.42  # Unit Clause-clause subsumption calls : 678
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 52
% 0.19/0.42  # BW rewrite match successes           : 5
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 34223
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.076 s
% 0.19/0.42  # System time              : 0.006 s
% 0.19/0.42  # Total time               : 0.083 s
% 0.19/0.42  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
