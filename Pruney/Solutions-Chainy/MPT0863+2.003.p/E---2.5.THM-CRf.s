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
% DateTime   : Thu Dec  3 10:59:17 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  148 (11874 expanded)
%              Number of clauses        :  123 (5423 expanded)
%              Number of leaves         :   12 (3121 expanded)
%              Depth                    :   30
%              Number of atoms          :  343 (28970 expanded)
%              Number of equality atoms :   84 (12369 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t19_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k2_tarski(X4,X5)))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & ( k2_mcart_1(X1) = X4
          | k2_mcart_1(X1) = X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_mcart_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t144_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t12_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
     => ( k1_mcart_1(X1) = X2
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k2_tarski(X4,X5)))
       => ( ( k1_mcart_1(X1) = X2
            | k1_mcart_1(X1) = X3 )
          & ( k2_mcart_1(X1) = X4
            | k2_mcart_1(X1) = X5 ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_mcart_1])).

fof(c_0_13,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k4_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_14,plain,(
    ! [X27,X28,X29] :
      ( r2_hidden(X27,X29)
      | r2_hidden(X28,X29)
      | X29 = k4_xboole_0(X29,k2_tarski(X27,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).

fof(c_0_15,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)))
    & ( k2_mcart_1(esk2_0) != esk5_0
      | k1_mcart_1(esk2_0) != esk3_0 )
    & ( k2_mcart_1(esk2_0) != esk6_0
      | k1_mcart_1(esk2_0) != esk3_0 )
    & ( k2_mcart_1(esk2_0) != esk5_0
      | k1_mcart_1(esk2_0) != esk4_0 )
    & ( k2_mcart_1(esk2_0) != esk6_0
      | k1_mcart_1(esk2_0) != esk4_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | X2 = k4_xboole_0(X2,k2_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X33,X34,X35] :
      ( ( r2_hidden(k1_mcart_1(X33),X34)
        | ~ r2_hidden(X33,k2_zfmisc_1(X34,X35)) )
      & ( r2_hidden(k2_mcart_1(X33),X35)
        | ~ r2_hidden(X33,k2_zfmisc_1(X34,X35)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X30,X31,X32] :
      ( ( r2_hidden(X30,X32)
        | ~ r1_tarski(k2_tarski(X30,X31),X32) )
      & ( r2_hidden(X31,X32)
        | ~ r1_tarski(k2_tarski(X30,X31),X32) )
      & ( ~ r2_hidden(X30,X32)
        | ~ r2_hidden(X31,X32)
        | r1_tarski(k2_tarski(X30,X31),X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_25,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( X2 = k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X3))
    | r2_hidden(X3,X2)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X23,X24,X25,X26] :
      ( ( r2_hidden(X23,X25)
        | ~ r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)) )
      & ( r2_hidden(X24,X26)
        | ~ r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)) )
      & ( ~ r2_hidden(X23,X25)
        | ~ r2_hidden(X24,X26)
        | r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X4,k2_enumset1(X1,X1,X1,X3))
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_20]),c_0_21])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_38,plain,(
    ! [X36,X37,X38] :
      ( ( k1_mcart_1(X36) = X37
        | ~ r2_hidden(X36,k2_zfmisc_1(k1_tarski(X37),X38)) )
      & ( r2_hidden(k2_mcart_1(X36),X38)
        | ~ r2_hidden(X36,k2_zfmisc_1(k1_tarski(X37),X38)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).

fof(c_0_39,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk6_0,X1)
    | r2_hidden(esk5_0,X1)
    | ~ r2_hidden(k2_mcart_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_29])).

cnf(c_0_44,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k2_mcart_1(esk2_0)),k2_zfmisc_1(X2,k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),X1))
    | r2_hidden(esk6_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_48,plain,(
    ! [X39,X40] :
      ( k1_mcart_1(k4_tarski(X39,X40)) = X39
      & k2_mcart_1(k4_tarski(X39,X40)) = X40 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk4_0,X1)
    | r2_hidden(esk3_0,X1)
    | ~ r2_hidden(k1_mcart_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_43])).

cnf(c_0_50,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_20]),c_0_21])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),X1),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)))
    | r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1))
    | r2_hidden(esk4_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk6_0
    | k1_mcart_1(esk2_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_55,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk6_0
    | r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)))
    | r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_53])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)))
    | k1_mcart_1(esk2_0) != esk4_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( k1_mcart_1(esk2_0) = esk4_0
    | r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_56]),c_0_52])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_enumset1(X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_20]),c_0_21])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0)))
    | r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_36])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)))
    | r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0),X1))
    | r2_hidden(k2_mcart_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_34])).

cnf(c_0_67,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k4_xboole_0(k2_enumset1(X2,X2,X2,X1),X3))
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk5_0
    | k1_mcart_1(esk2_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_70,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk5_0
    | r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_65]),c_0_52])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk5_0,k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0),X1))
    | r2_hidden(esk6_0,k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0),X1))
    | r2_hidden(k2_mcart_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_66])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X3))
    | r2_hidden(X4,k2_enumset1(X2,X2,X2,X3))
    | ~ r2_hidden(X2,k2_enumset1(X4,X4,X4,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_42])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk5_0,k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)))
    | r2_hidden(esk6_0,k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_64])).

cnf(c_0_74,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_20]),c_0_21])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,k4_xboole_0(k2_enumset1(X2,X2,X2,X3),X4))
    | r2_hidden(X5,k4_xboole_0(k2_enumset1(X2,X2,X2,X3),X4))
    | r2_hidden(X3,X4)
    | ~ r2_hidden(X3,k2_enumset1(X5,X5,X5,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_59])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk5_0,k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0),X1))
    | r2_hidden(k2_mcart_1(esk2_0),X1)
    | ~ r2_hidden(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk6_0,esk6_0,esk6_0,X1))
    | r2_hidden(esk5_0,k2_enumset1(X2,X2,X2,k2_mcart_1(esk2_0)))
    | r2_hidden(X2,k2_enumset1(esk6_0,esk6_0,esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_80,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X1))
    | ~ r2_hidden(X2,k2_enumset1(X3,X3,X3,X1)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_64])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk5_0,k4_xboole_0(k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)),X2))
    | r2_hidden(esk6_0,k4_xboole_0(k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)),X2))
    | r2_hidden(k2_mcart_1(esk2_0),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_68])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X3))
    | r2_hidden(X4,k2_enumset1(X2,X2,X2,X3))
    | ~ r2_hidden(X3,k2_enumset1(X4,X4,X4,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_64])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),k4_xboole_0(k2_enumset1(X1,X1,X1,esk3_0),X2))
    | r2_hidden(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk5_0,k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0),k2_enumset1(esk6_0,esk6_0,esk6_0,X1)))
    | r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk6_0,esk6_0,esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_42])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)))
    | r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk6_0,esk6_0,esk6_0,X1)) ),
    inference(ef,[status(thm)],[c_0_79])).

cnf(c_0_87,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_88,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_42])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk5_0,k4_xboole_0(k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)),X2))
    | r2_hidden(esk6_0,k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)))
    | r2_hidden(k2_mcart_1(esk2_0),X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_90,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X3))
    | ~ r2_hidden(X2,k2_enumset1(X1,X1,X1,X3)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_42])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),k2_enumset1(X1,X1,X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_77])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | ~ r2_hidden(k1_mcart_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_84])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk6_0,esk6_0,esk6_0,X1))
    | ~ r2_hidden(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_85])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk6_0,esk6_0,esk6_0,X1))
    | r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X2,X2,X2,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_86])).

cnf(c_0_95,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_88])])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk6_0,k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)))
    | r2_hidden(k2_mcart_1(esk2_0),X2)
    | ~ r2_hidden(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_89])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k2_enumset1(X1,X1,X1,k1_mcart_1(esk2_0)),k2_enumset1(X1,X1,X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk3_0,k2_enumset1(X1,X1,X1,k1_mcart_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_64])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_64])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X1,X1,X1,esk5_0))
    | r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X2,X2,X2,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X1,X1,X1,esk5_0))
    | r2_hidden(esk6_0,k2_enumset1(X2,X2,X2,k2_mcart_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_96,c_0_64])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk6_0,esk6_0,esk6_0,X1))
    | r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X2)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_86])).

cnf(c_0_103,negated_conjecture,
    ( k2_enumset1(X1,X1,X1,k1_mcart_1(esk2_0)) = k2_enumset1(X1,X1,X1,esk3_0)
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,esk3_0),k2_enumset1(X1,X1,X1,k1_mcart_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k2_enumset1(X1,X1,X1,esk3_0),k2_enumset1(X1,X1,X1,k1_mcart_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_98])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k2_mcart_1(esk2_0)),k2_zfmisc_1(X2,k2_enumset1(esk6_0,esk6_0,esk6_0,esk5_0)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_99])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)),k2_enumset1(X1,X1,X1,esk6_0))
    | r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X2,X2,X2,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(k2_enumset1(X1,X1,X1,esk6_0),k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)))
    | r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X2,X2,X2,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_101])).

cnf(c_0_108,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X1))
    | r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X2,X2,X2,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_95])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X1))
    | r2_hidden(esk6_0,k2_enumset1(X2,X2,X2,k2_mcart_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_96,c_0_42])).

cnf(c_0_110,negated_conjecture,
    ( k2_enumset1(X1,X1,X1,k1_mcart_1(esk2_0)) = k2_enumset1(X1,X1,X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104])])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X1),k2_enumset1(esk6_0,esk6_0,esk6_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_64])).

cnf(c_0_112,negated_conjecture,
    ( k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)) = k2_enumset1(X1,X1,X1,esk6_0)
    | r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X2,X2,X2,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_106]),c_0_107])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(esk6_0,esk6_0,esk6_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_42])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)),k2_enumset1(X1,X1,X1,esk6_0))
    | r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X2)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_108])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(k2_enumset1(X1,X1,X1,esk6_0),k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)))
    | r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X2)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_109])).

cnf(c_0_116,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk6_0
    | k1_mcart_1(esk2_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_117,negated_conjecture,
    ( k1_mcart_1(X1) = k1_mcart_1(esk2_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_110]),c_0_95]),c_0_110])).

cnf(c_0_118,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X1),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[c_0_111,c_0_95])).

cnf(c_0_119,negated_conjecture,
    ( k1_mcart_1(X1) = k2_mcart_1(esk2_0)
    | r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X2,X2,X2,esk5_0))
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk6_0,esk6_0,esk6_0,k2_mcart_1(esk2_0)),X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_112]),c_0_95])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[c_0_113,c_0_95])).

cnf(c_0_121,negated_conjecture,
    ( k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)) = k2_enumset1(X1,X1,X1,esk6_0)
    | r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_114]),c_0_115])).

cnf(c_0_122,plain,
    ( r2_hidden(X1,k4_xboole_0(k2_enumset1(X1,X1,X1,X2),X3))
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_63,c_0_42])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)))
    | k1_mcart_1(esk2_0) != esk3_0 ),
    inference(spm,[status(thm)],[c_0_116,c_0_55])).

cnf(c_0_124,negated_conjecture,
    ( k1_mcart_1(esk2_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_52])).

cnf(c_0_125,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk6_0
    | r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X1,X1,X1,esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_52])).

cnf(c_0_126,negated_conjecture,
    ( k1_mcart_1(X1) = k2_mcart_1(esk2_0)
    | r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X2))
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk6_0,esk6_0,esk6_0,k2_mcart_1(esk2_0)),X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_121]),c_0_95])).

cnf(c_0_127,plain,
    ( r2_hidden(X1,k4_xboole_0(k2_enumset1(X2,X2,X2,X3),X4))
    | r2_hidden(X5,k4_xboole_0(k2_enumset1(X2,X2,X2,X3),X4))
    | r2_hidden(X2,X4)
    | ~ r2_hidden(X2,k2_enumset1(X5,X5,X5,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_122])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_124])])).

cnf(c_0_129,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X1,X1,X1,esk5_0))
    | k1_mcart_1(esk2_0) != esk3_0 ),
    inference(spm,[status(thm)],[c_0_116,c_0_125])).

cnf(c_0_130,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk6_0
    | r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_120]),c_0_52])).

cnf(c_0_131,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,X1),X2))
    | r2_hidden(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_132,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X1,X1,X1,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_124])])).

cnf(c_0_133,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X1))
    | k1_mcart_1(esk2_0) != esk3_0 ),
    inference(spm,[status(thm)],[c_0_116,c_0_130])).

cnf(c_0_134,negated_conjecture,
    ( r2_hidden(esk5_0,X1)
    | ~ r2_hidden(k2_mcart_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_131])).

cnf(c_0_135,negated_conjecture,
    ( r1_tarski(k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)),k2_enumset1(X2,X2,X2,esk5_0))
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_132])).

cnf(c_0_136,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_124])])).

cnf(c_0_137,negated_conjecture,
    ( r2_hidden(esk5_0,k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_134,c_0_64])).

cnf(c_0_138,negated_conjecture,
    ( r1_tarski(k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_139,negated_conjecture,
    ( r1_tarski(k2_enumset1(X1,X1,X1,esk5_0),k2_enumset1(X2,X2,X2,k2_mcart_1(esk2_0)))
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,k2_mcart_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_137])).

cnf(c_0_140,negated_conjecture,
    ( r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_134,c_0_42])).

cnf(c_0_141,negated_conjecture,
    ( k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)) = k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)
    | ~ r1_tarski(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_138])).

cnf(c_0_142,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_143,negated_conjecture,
    ( k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)) = k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_141,c_0_142])])).

cnf(c_0_144,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk5_0
    | k1_mcart_1(esk2_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_145,negated_conjecture,
    ( k1_mcart_1(X1) = k2_mcart_1(esk2_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_143])).

cnf(c_0_146,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_144,c_0_124])])).

cnf(c_0_147,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_118]),c_0_52]),c_0_146]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.83/2.01  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 1.83/2.01  # and selection function SelectNegativeLiterals.
% 1.83/2.01  #
% 1.83/2.01  # Preprocessing time       : 0.027 s
% 1.83/2.01  # Presaturation interreduction done
% 1.83/2.01  
% 1.83/2.01  # Proof found!
% 1.83/2.01  # SZS status Theorem
% 1.83/2.01  # SZS output start CNFRefutation
% 1.83/2.01  fof(t19_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k2_tarski(X4,X5)))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&(k2_mcart_1(X1)=X4|k2_mcart_1(X1)=X5))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_mcart_1)).
% 1.83/2.01  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.83/2.01  fof(t144_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 1.83/2.01  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.83/2.01  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.83/2.01  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.83/2.01  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.83/2.01  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.83/2.01  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.83/2.01  fof(t12_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.83/2.01  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.83/2.01  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.83/2.01  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k2_tarski(X4,X5)))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&(k2_mcart_1(X1)=X4|k2_mcart_1(X1)=X5)))), inference(assume_negation,[status(cth)],[t19_mcart_1])).
% 1.83/2.01  fof(c_0_13, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 1.83/2.01  fof(c_0_14, plain, ![X27, X28, X29]:(r2_hidden(X27,X29)|r2_hidden(X28,X29)|X29=k4_xboole_0(X29,k2_tarski(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).
% 1.83/2.01  fof(c_0_15, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.83/2.01  fof(c_0_16, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.83/2.01  fof(c_0_17, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)))&(((k2_mcart_1(esk2_0)!=esk5_0|k1_mcart_1(esk2_0)!=esk3_0)&(k2_mcart_1(esk2_0)!=esk6_0|k1_mcart_1(esk2_0)!=esk3_0))&((k2_mcart_1(esk2_0)!=esk5_0|k1_mcart_1(esk2_0)!=esk4_0)&(k2_mcart_1(esk2_0)!=esk6_0|k1_mcart_1(esk2_0)!=esk4_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 1.83/2.01  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.83/2.01  cnf(c_0_19, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|X2=k4_xboole_0(X2,k2_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.83/2.01  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.83/2.01  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.83/2.01  fof(c_0_22, plain, ![X33, X34, X35]:((r2_hidden(k1_mcart_1(X33),X34)|~r2_hidden(X33,k2_zfmisc_1(X34,X35)))&(r2_hidden(k2_mcart_1(X33),X35)|~r2_hidden(X33,k2_zfmisc_1(X34,X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 1.83/2.01  cnf(c_0_23, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.83/2.01  fof(c_0_24, plain, ![X30, X31, X32]:(((r2_hidden(X30,X32)|~r1_tarski(k2_tarski(X30,X31),X32))&(r2_hidden(X31,X32)|~r1_tarski(k2_tarski(X30,X31),X32)))&(~r2_hidden(X30,X32)|~r2_hidden(X31,X32)|r1_tarski(k2_tarski(X30,X31),X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 1.83/2.01  fof(c_0_25, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.83/2.01  cnf(c_0_26, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_18])).
% 1.83/2.01  cnf(c_0_27, plain, (X2=k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X3))|r2_hidden(X3,X2)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 1.83/2.01  cnf(c_0_28, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.83/2.01  cnf(c_0_29, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_20]), c_0_20]), c_0_21]), c_0_21])).
% 1.83/2.01  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.83/2.01  cnf(c_0_31, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.83/2.01  fof(c_0_32, plain, ![X23, X24, X25, X26]:(((r2_hidden(X23,X25)|~r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)))&(r2_hidden(X24,X26)|~r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26))))&(~r2_hidden(X23,X25)|~r2_hidden(X24,X26)|r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 1.83/2.01  cnf(c_0_33, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|~r2_hidden(X4,k2_enumset1(X1,X1,X1,X3))|~r2_hidden(X4,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 1.83/2.01  cnf(c_0_34, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.83/2.01  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_20]), c_0_21])).
% 1.83/2.01  cnf(c_0_36, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 1.83/2.01  cnf(c_0_37, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.83/2.01  fof(c_0_38, plain, ![X36, X37, X38]:((k1_mcart_1(X36)=X37|~r2_hidden(X36,k2_zfmisc_1(k1_tarski(X37),X38)))&(r2_hidden(k2_mcart_1(X36),X38)|~r2_hidden(X36,k2_zfmisc_1(k1_tarski(X37),X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).
% 1.83/2.01  fof(c_0_39, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.83/2.01  cnf(c_0_40, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.83/2.01  cnf(c_0_41, negated_conjecture, (r2_hidden(esk6_0,X1)|r2_hidden(esk5_0,X1)|~r2_hidden(k2_mcart_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.83/2.01  cnf(c_0_42, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.83/2.01  cnf(c_0_43, negated_conjecture, (r2_hidden(k1_mcart_1(esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_29])).
% 1.83/2.01  cnf(c_0_44, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.83/2.01  cnf(c_0_45, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.83/2.01  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(X1,k2_mcart_1(esk2_0)),k2_zfmisc_1(X2,k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_34])).
% 1.83/2.01  cnf(c_0_47, negated_conjecture, (r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),X1))|r2_hidden(esk6_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.83/2.01  fof(c_0_48, plain, ![X39, X40]:(k1_mcart_1(k4_tarski(X39,X40))=X39&k2_mcart_1(k4_tarski(X39,X40))=X40), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 1.83/2.01  cnf(c_0_49, negated_conjecture, (r2_hidden(esk4_0,X1)|r2_hidden(esk3_0,X1)|~r2_hidden(k1_mcart_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_33, c_0_43])).
% 1.83/2.01  cnf(c_0_50, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_20]), c_0_21])).
% 1.83/2.01  cnf(c_0_51, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),X1),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)))|r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),X1))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.83/2.01  cnf(c_0_52, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.83/2.01  cnf(c_0_53, negated_conjecture, (r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1))|r2_hidden(esk4_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1))), inference(spm,[status(thm)],[c_0_49, c_0_42])).
% 1.83/2.01  cnf(c_0_54, negated_conjecture, (k2_mcart_1(esk2_0)!=esk6_0|k1_mcart_1(esk2_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.83/2.01  cnf(c_0_55, negated_conjecture, (k2_mcart_1(esk2_0)=esk6_0|r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 1.83/2.01  cnf(c_0_56, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)))|r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1))), inference(spm,[status(thm)],[c_0_46, c_0_53])).
% 1.83/2.01  cnf(c_0_57, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.83/2.01  cnf(c_0_58, negated_conjecture, (r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)))|k1_mcart_1(esk2_0)!=esk4_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 1.83/2.01  cnf(c_0_59, negated_conjecture, (k1_mcart_1(esk2_0)=esk4_0|r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_56]), c_0_52])).
% 1.83/2.01  cnf(c_0_60, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.83/2.01  cnf(c_0_61, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_enumset1(X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_20]), c_0_21])).
% 1.83/2.01  cnf(c_0_62, negated_conjecture, (r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0)))|r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 1.83/2.01  cnf(c_0_63, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_60])).
% 1.83/2.01  cnf(c_0_64, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_61, c_0_36])).
% 1.83/2.01  cnf(c_0_65, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)))|r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0)))), inference(spm,[status(thm)],[c_0_46, c_0_62])).
% 1.83/2.01  cnf(c_0_66, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0),X1))|r2_hidden(k2_mcart_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_63, c_0_34])).
% 1.83/2.01  cnf(c_0_67, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.83/2.01  cnf(c_0_68, plain, (r2_hidden(X1,k4_xboole_0(k2_enumset1(X2,X2,X2,X1),X3))|r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 1.83/2.01  cnf(c_0_69, negated_conjecture, (k2_mcart_1(esk2_0)!=esk5_0|k1_mcart_1(esk2_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.83/2.01  cnf(c_0_70, negated_conjecture, (k2_mcart_1(esk2_0)=esk5_0|r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_65]), c_0_52])).
% 1.83/2.01  cnf(c_0_71, negated_conjecture, (r2_hidden(esk5_0,k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0),X1))|r2_hidden(esk6_0,k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0),X1))|r2_hidden(k2_mcart_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_41, c_0_66])).
% 1.83/2.01  cnf(c_0_72, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X3))|r2_hidden(X4,k2_enumset1(X2,X2,X2,X3))|~r2_hidden(X2,k2_enumset1(X4,X4,X4,X1))), inference(spm,[status(thm)],[c_0_33, c_0_42])).
% 1.83/2.01  cnf(c_0_73, negated_conjecture, (r2_hidden(esk5_0,k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)))|r2_hidden(esk6_0,k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)))), inference(spm,[status(thm)],[c_0_41, c_0_64])).
% 1.83/2.01  cnf(c_0_74, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_20]), c_0_21])).
% 1.83/2.01  cnf(c_0_75, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.83/2.01  cnf(c_0_76, plain, (r2_hidden(X1,k4_xboole_0(k2_enumset1(X2,X2,X2,X3),X4))|r2_hidden(X5,k4_xboole_0(k2_enumset1(X2,X2,X2,X3),X4))|r2_hidden(X3,X4)|~r2_hidden(X3,k2_enumset1(X5,X5,X5,X1))), inference(spm,[status(thm)],[c_0_33, c_0_68])).
% 1.83/2.01  cnf(c_0_77, negated_conjecture, (r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_59])).
% 1.83/2.01  cnf(c_0_78, negated_conjecture, (r2_hidden(esk5_0,k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0),X1))|r2_hidden(k2_mcart_1(esk2_0),X1)|~r2_hidden(esk6_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_71])).
% 1.83/2.01  cnf(c_0_79, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk6_0,esk6_0,esk6_0,X1))|r2_hidden(esk5_0,k2_enumset1(X2,X2,X2,k2_mcart_1(esk2_0)))|r2_hidden(X2,k2_enumset1(esk6_0,esk6_0,esk6_0,X1))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 1.83/2.01  cnf(c_0_80, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X1))|~r2_hidden(X2,k2_enumset1(X3,X3,X3,X1))), inference(spm,[status(thm)],[c_0_74, c_0_64])).
% 1.83/2.01  cnf(c_0_81, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_75])).
% 1.83/2.01  cnf(c_0_82, negated_conjecture, (r2_hidden(esk5_0,k4_xboole_0(k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)),X2))|r2_hidden(esk6_0,k4_xboole_0(k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)),X2))|r2_hidden(k2_mcart_1(esk2_0),X2)), inference(spm,[status(thm)],[c_0_41, c_0_68])).
% 1.83/2.01  cnf(c_0_83, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X3))|r2_hidden(X4,k2_enumset1(X2,X2,X2,X3))|~r2_hidden(X3,k2_enumset1(X4,X4,X4,X1))), inference(spm,[status(thm)],[c_0_33, c_0_64])).
% 1.83/2.01  cnf(c_0_84, negated_conjecture, (r2_hidden(k1_mcart_1(esk2_0),k4_xboole_0(k2_enumset1(X1,X1,X1,esk3_0),X2))|r2_hidden(esk3_0,X2)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 1.83/2.01  cnf(c_0_85, negated_conjecture, (r2_hidden(esk5_0,k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0),k2_enumset1(esk6_0,esk6_0,esk6_0,X1)))|r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk6_0,esk6_0,esk6_0,X1))), inference(spm,[status(thm)],[c_0_78, c_0_42])).
% 1.83/2.01  cnf(c_0_86, negated_conjecture, (r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)))|r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk6_0,esk6_0,esk6_0,X1))), inference(ef,[status(thm)],[c_0_79])).
% 1.83/2.01  cnf(c_0_87, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.83/2.01  cnf(c_0_88, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_80, c_0_42])).
% 1.83/2.01  cnf(c_0_89, negated_conjecture, (r2_hidden(esk5_0,k4_xboole_0(k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)),X2))|r2_hidden(esk6_0,k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)))|r2_hidden(k2_mcart_1(esk2_0),X2)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 1.83/2.01  cnf(c_0_90, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X3))|~r2_hidden(X2,k2_enumset1(X1,X1,X1,X3))), inference(spm,[status(thm)],[c_0_74, c_0_42])).
% 1.83/2.01  cnf(c_0_91, negated_conjecture, (r2_hidden(k1_mcart_1(esk2_0),k2_enumset1(X1,X1,X1,esk3_0))), inference(spm,[status(thm)],[c_0_83, c_0_77])).
% 1.83/2.01  cnf(c_0_92, negated_conjecture, (r2_hidden(esk3_0,X1)|~r2_hidden(k1_mcart_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_26, c_0_84])).
% 1.83/2.01  cnf(c_0_93, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk6_0,esk6_0,esk6_0,X1))|~r2_hidden(esk5_0,k2_enumset1(esk6_0,esk6_0,esk6_0,X1))), inference(spm,[status(thm)],[c_0_26, c_0_85])).
% 1.83/2.01  cnf(c_0_94, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk6_0,esk6_0,esk6_0,X1))|r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X2,X2,X2,esk5_0))), inference(spm,[status(thm)],[c_0_83, c_0_86])).
% 1.83/2.01  cnf(c_0_95, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_88])])).
% 1.83/2.01  cnf(c_0_96, negated_conjecture, (r2_hidden(esk6_0,k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)))|r2_hidden(k2_mcart_1(esk2_0),X2)|~r2_hidden(esk5_0,X2)), inference(spm,[status(thm)],[c_0_26, c_0_89])).
% 1.83/2.01  cnf(c_0_97, negated_conjecture, (r1_tarski(k2_enumset1(X1,X1,X1,k1_mcart_1(esk2_0)),k2_enumset1(X1,X1,X1,esk3_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 1.83/2.01  cnf(c_0_98, negated_conjecture, (r2_hidden(esk3_0,k2_enumset1(X1,X1,X1,k1_mcart_1(esk2_0)))), inference(spm,[status(thm)],[c_0_92, c_0_64])).
% 1.83/2.01  cnf(c_0_99, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk5_0))), inference(spm,[status(thm)],[c_0_93, c_0_64])).
% 1.83/2.01  cnf(c_0_100, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X1,X1,X1,esk5_0))|r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X2,X2,X2,esk6_0))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 1.83/2.01  cnf(c_0_101, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X1,X1,X1,esk5_0))|r2_hidden(esk6_0,k2_enumset1(X2,X2,X2,k2_mcart_1(esk2_0)))), inference(spm,[status(thm)],[c_0_96, c_0_64])).
% 1.83/2.01  cnf(c_0_102, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk6_0,esk6_0,esk6_0,X1))|r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X2))), inference(spm,[status(thm)],[c_0_72, c_0_86])).
% 1.83/2.01  cnf(c_0_103, negated_conjecture, (k2_enumset1(X1,X1,X1,k1_mcart_1(esk2_0))=k2_enumset1(X1,X1,X1,esk3_0)|~r1_tarski(k2_enumset1(X1,X1,X1,esk3_0),k2_enumset1(X1,X1,X1,k1_mcart_1(esk2_0)))), inference(spm,[status(thm)],[c_0_87, c_0_97])).
% 1.83/2.01  cnf(c_0_104, negated_conjecture, (r1_tarski(k2_enumset1(X1,X1,X1,esk3_0),k2_enumset1(X1,X1,X1,k1_mcart_1(esk2_0)))), inference(spm,[status(thm)],[c_0_90, c_0_98])).
% 1.83/2.01  cnf(c_0_105, negated_conjecture, (r2_hidden(k4_tarski(X1,k2_mcart_1(esk2_0)),k2_zfmisc_1(X2,k2_enumset1(esk6_0,esk6_0,esk6_0,esk5_0)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_99])).
% 1.83/2.01  cnf(c_0_106, negated_conjecture, (r1_tarski(k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)),k2_enumset1(X1,X1,X1,esk6_0))|r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X2,X2,X2,esk5_0))), inference(spm,[status(thm)],[c_0_90, c_0_100])).
% 1.83/2.01  cnf(c_0_107, negated_conjecture, (r1_tarski(k2_enumset1(X1,X1,X1,esk6_0),k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)))|r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X2,X2,X2,esk5_0))), inference(spm,[status(thm)],[c_0_90, c_0_101])).
% 1.83/2.01  cnf(c_0_108, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X1))|r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X2,X2,X2,esk6_0))), inference(spm,[status(thm)],[c_0_102, c_0_95])).
% 1.83/2.01  cnf(c_0_109, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X1))|r2_hidden(esk6_0,k2_enumset1(X2,X2,X2,k2_mcart_1(esk2_0)))), inference(spm,[status(thm)],[c_0_96, c_0_42])).
% 1.83/2.01  cnf(c_0_110, negated_conjecture, (k2_enumset1(X1,X1,X1,k1_mcart_1(esk2_0))=k2_enumset1(X1,X1,X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_104])])).
% 1.83/2.01  cnf(c_0_111, negated_conjecture, (r2_hidden(k4_tarski(X1,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X1),k2_enumset1(esk6_0,esk6_0,esk6_0,esk5_0)))), inference(spm,[status(thm)],[c_0_105, c_0_64])).
% 1.83/2.01  cnf(c_0_112, negated_conjecture, (k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0))=k2_enumset1(X1,X1,X1,esk6_0)|r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X2,X2,X2,esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_106]), c_0_107])).
% 1.83/2.01  cnf(c_0_113, negated_conjecture, (r2_hidden(k4_tarski(X1,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(esk6_0,esk6_0,esk6_0,esk5_0)))), inference(spm,[status(thm)],[c_0_105, c_0_42])).
% 1.83/2.01  cnf(c_0_114, negated_conjecture, (r1_tarski(k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)),k2_enumset1(X1,X1,X1,esk6_0))|r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X2))), inference(spm,[status(thm)],[c_0_90, c_0_108])).
% 1.83/2.01  cnf(c_0_115, negated_conjecture, (r1_tarski(k2_enumset1(X1,X1,X1,esk6_0),k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)))|r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X2))), inference(spm,[status(thm)],[c_0_90, c_0_109])).
% 1.83/2.01  cnf(c_0_116, negated_conjecture, (k2_mcart_1(esk2_0)!=esk6_0|k1_mcart_1(esk2_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.83/2.01  cnf(c_0_117, negated_conjecture, (k1_mcart_1(X1)=k1_mcart_1(esk2_0)|~r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_110]), c_0_95]), c_0_110])).
% 1.83/2.01  cnf(c_0_118, negated_conjecture, (r2_hidden(k4_tarski(X1,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X1),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)))), inference(rw,[status(thm)],[c_0_111, c_0_95])).
% 1.83/2.01  cnf(c_0_119, negated_conjecture, (k1_mcart_1(X1)=k2_mcart_1(esk2_0)|r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X2,X2,X2,esk5_0))|~r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk6_0,esk6_0,esk6_0,k2_mcart_1(esk2_0)),X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_112]), c_0_95])).
% 1.83/2.01  cnf(c_0_120, negated_conjecture, (r2_hidden(k4_tarski(X1,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(esk5_0,esk5_0,esk5_0,esk6_0)))), inference(rw,[status(thm)],[c_0_113, c_0_95])).
% 1.83/2.01  cnf(c_0_121, negated_conjecture, (k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0))=k2_enumset1(X1,X1,X1,esk6_0)|r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_114]), c_0_115])).
% 1.83/2.01  cnf(c_0_122, plain, (r2_hidden(X1,k4_xboole_0(k2_enumset1(X1,X1,X1,X2),X3))|r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_63, c_0_42])).
% 1.83/2.01  cnf(c_0_123, negated_conjecture, (r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)))|k1_mcart_1(esk2_0)!=esk3_0), inference(spm,[status(thm)],[c_0_116, c_0_55])).
% 1.83/2.01  cnf(c_0_124, negated_conjecture, (k1_mcart_1(esk2_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_52])).
% 1.83/2.01  cnf(c_0_125, negated_conjecture, (k2_mcart_1(esk2_0)=esk6_0|r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X1,X1,X1,esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_52])).
% 1.83/2.01  cnf(c_0_126, negated_conjecture, (k1_mcart_1(X1)=k2_mcart_1(esk2_0)|r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X2))|~r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk6_0,esk6_0,esk6_0,k2_mcart_1(esk2_0)),X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_121]), c_0_95])).
% 1.83/2.01  cnf(c_0_127, plain, (r2_hidden(X1,k4_xboole_0(k2_enumset1(X2,X2,X2,X3),X4))|r2_hidden(X5,k4_xboole_0(k2_enumset1(X2,X2,X2,X3),X4))|r2_hidden(X2,X4)|~r2_hidden(X2,k2_enumset1(X5,X5,X5,X1))), inference(spm,[status(thm)],[c_0_33, c_0_122])).
% 1.83/2.01  cnf(c_0_128, negated_conjecture, (r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_124])])).
% 1.83/2.01  cnf(c_0_129, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X1,X1,X1,esk5_0))|k1_mcart_1(esk2_0)!=esk3_0), inference(spm,[status(thm)],[c_0_116, c_0_125])).
% 1.83/2.01  cnf(c_0_130, negated_conjecture, (k2_mcart_1(esk2_0)=esk6_0|r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_120]), c_0_52])).
% 1.83/2.01  cnf(c_0_131, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,X1),X2))|r2_hidden(esk5_0,X2)), inference(spm,[status(thm)],[c_0_127, c_0_128])).
% 1.83/2.01  cnf(c_0_132, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(X1,X1,X1,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_124])])).
% 1.83/2.01  cnf(c_0_133, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X1))|k1_mcart_1(esk2_0)!=esk3_0), inference(spm,[status(thm)],[c_0_116, c_0_130])).
% 1.83/2.01  cnf(c_0_134, negated_conjecture, (r2_hidden(esk5_0,X1)|~r2_hidden(k2_mcart_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_26, c_0_131])).
% 1.83/2.01  cnf(c_0_135, negated_conjecture, (r1_tarski(k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)),k2_enumset1(X2,X2,X2,esk5_0))|~r2_hidden(X1,k2_enumset1(X2,X2,X2,esk5_0))), inference(spm,[status(thm)],[c_0_74, c_0_132])).
% 1.83/2.01  cnf(c_0_136, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_133, c_0_124])])).
% 1.83/2.01  cnf(c_0_137, negated_conjecture, (r2_hidden(esk5_0,k2_enumset1(X1,X1,X1,k2_mcart_1(esk2_0)))), inference(spm,[status(thm)],[c_0_134, c_0_64])).
% 1.83/2.01  cnf(c_0_138, negated_conjecture, (r1_tarski(k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 1.83/2.01  cnf(c_0_139, negated_conjecture, (r1_tarski(k2_enumset1(X1,X1,X1,esk5_0),k2_enumset1(X2,X2,X2,k2_mcart_1(esk2_0)))|~r2_hidden(X1,k2_enumset1(X2,X2,X2,k2_mcart_1(esk2_0)))), inference(spm,[status(thm)],[c_0_74, c_0_137])).
% 1.83/2.01  cnf(c_0_140, negated_conjecture, (r2_hidden(esk5_0,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),X1))), inference(spm,[status(thm)],[c_0_134, c_0_42])).
% 1.83/2.01  cnf(c_0_141, negated_conjecture, (k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0))=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)|~r1_tarski(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)))), inference(spm,[status(thm)],[c_0_87, c_0_138])).
% 1.83/2.01  cnf(c_0_142, negated_conjecture, (r1_tarski(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)))), inference(spm,[status(thm)],[c_0_139, c_0_140])).
% 1.83/2.01  cnf(c_0_143, negated_conjecture, (k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0))=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_141, c_0_142])])).
% 1.83/2.01  cnf(c_0_144, negated_conjecture, (k2_mcart_1(esk2_0)!=esk5_0|k1_mcart_1(esk2_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.83/2.01  cnf(c_0_145, negated_conjecture, (k1_mcart_1(X1)=k2_mcart_1(esk2_0)|~r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),X2))), inference(spm,[status(thm)],[c_0_50, c_0_143])).
% 1.83/2.01  cnf(c_0_146, negated_conjecture, (k2_mcart_1(esk2_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_144, c_0_124])])).
% 1.83/2.01  cnf(c_0_147, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_118]), c_0_52]), c_0_146]), ['proof']).
% 1.83/2.01  # SZS output end CNFRefutation
% 1.83/2.01  # Proof object total steps             : 148
% 1.83/2.01  # Proof object clause steps            : 123
% 1.83/2.01  # Proof object formula steps           : 25
% 1.83/2.01  # Proof object conjectures             : 87
% 1.83/2.01  # Proof object clause conjectures      : 84
% 1.83/2.01  # Proof object formula conjectures     : 3
% 1.83/2.01  # Proof object initial clauses used    : 22
% 1.83/2.01  # Proof object initial formulas used   : 12
% 1.83/2.01  # Proof object generating inferences   : 83
% 1.83/2.01  # Proof object simplifying inferences  : 50
% 1.83/2.01  # Training examples: 0 positive, 0 negative
% 1.83/2.01  # Parsed axioms                        : 12
% 1.83/2.01  # Removed by relevancy pruning/SinE    : 0
% 1.83/2.01  # Initial clauses                      : 30
% 1.83/2.01  # Removed in clause preprocessing      : 3
% 1.83/2.01  # Initial clauses in saturation        : 27
% 1.83/2.01  # Processed clauses                    : 3253
% 1.83/2.01  # ...of these trivial                  : 102
% 1.83/2.01  # ...subsumed                          : 1910
% 1.83/2.01  # ...remaining for further processing  : 1241
% 1.83/2.01  # Other redundant clauses eliminated   : 165
% 1.83/2.01  # Clauses deleted for lack of memory   : 0
% 1.83/2.01  # Backward-subsumed                    : 199
% 1.83/2.01  # Backward-rewritten                   : 692
% 1.83/2.01  # Generated clauses                    : 155170
% 1.83/2.01  # ...of the previous two non-trivial   : 149715
% 1.83/2.01  # Contextual simplify-reflections      : 19
% 1.83/2.01  # Paramodulations                      : 154840
% 1.83/2.01  # Factorizations                       : 162
% 1.83/2.01  # Equation resolutions                 : 165
% 1.83/2.01  # Propositional unsat checks           : 0
% 1.83/2.01  #    Propositional check models        : 0
% 1.83/2.01  #    Propositional check unsatisfiable : 0
% 1.83/2.01  #    Propositional clauses             : 0
% 1.83/2.01  #    Propositional clauses after purity: 0
% 1.83/2.01  #    Propositional unsat core size     : 0
% 1.83/2.01  #    Propositional preprocessing time  : 0.000
% 1.83/2.01  #    Propositional encoding time       : 0.000
% 1.83/2.01  #    Propositional solver time         : 0.000
% 1.83/2.01  #    Success case prop preproc time    : 0.000
% 1.83/2.01  #    Success case prop encoding time   : 0.000
% 1.83/2.01  #    Success case prop solver time     : 0.000
% 1.83/2.01  # Current number of processed clauses  : 317
% 1.83/2.01  #    Positive orientable unit clauses  : 40
% 1.83/2.01  #    Positive unorientable unit clauses: 1
% 1.83/2.01  #    Negative unit clauses             : 2
% 1.83/2.01  #    Non-unit-clauses                  : 274
% 1.83/2.01  # Current number of unprocessed clauses: 146039
% 1.83/2.01  # ...number of literals in the above   : 629432
% 1.83/2.01  # Current number of archived formulas  : 0
% 1.83/2.01  # Current number of archived clauses   : 922
% 1.83/2.01  # Clause-clause subsumption calls (NU) : 194394
% 1.83/2.01  # Rec. Clause-clause subsumption calls : 114433
% 1.83/2.01  # Non-unit clause-clause subsumptions  : 2071
% 1.83/2.01  # Unit Clause-clause subsumption calls : 3979
% 1.83/2.01  # Rewrite failures with RHS unbound    : 0
% 1.83/2.01  # BW rewrite match attempts            : 969
% 1.83/2.01  # BW rewrite match successes           : 160
% 1.83/2.01  # Condensation attempts                : 0
% 1.83/2.01  # Condensation successes               : 0
% 1.83/2.01  # Termbank termtop insertions          : 5560027
% 1.83/2.01  
% 1.83/2.01  # -------------------------------------------------
% 1.83/2.01  # User time                : 1.609 s
% 1.83/2.01  # System time              : 0.060 s
% 1.83/2.01  # Total time               : 1.669 s
% 1.83/2.01  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
