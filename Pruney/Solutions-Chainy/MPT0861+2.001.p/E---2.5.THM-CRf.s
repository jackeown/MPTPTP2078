%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:10 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 240 expanded)
%              Number of clauses        :   37 (  99 expanded)
%              Number of leaves         :   13 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  169 ( 453 expanded)
%              Number of equality atoms :   60 ( 270 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & k2_mcart_1(X1) = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_mcart_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t144_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t11_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) )
     => ( ! [X4,X5] : X1 != k4_tarski(X4,X5)
        | r2_hidden(X1,k2_zfmisc_1(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t13_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & k2_mcart_1(X1) = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

fof(t12_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
     => ( k1_mcart_1(X1) = X2
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))
       => ( ( k1_mcart_1(X1) = X2
            | k1_mcart_1(X1) = X3 )
          & k2_mcart_1(X1) = X4 ) ) ),
    inference(assume_negation,[status(cth)],[t17_mcart_1])).

fof(c_0_14,plain,(
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

fof(c_0_15,plain,(
    ! [X23,X24,X25] :
      ( r2_hidden(X23,X25)
      | r2_hidden(X24,X25)
      | X25 = k4_xboole_0(X25,k2_tarski(X23,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).

fof(c_0_16,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0)))
    & ( k1_mcart_1(esk2_0) != esk3_0
      | k2_mcart_1(esk2_0) != esk5_0 )
    & ( k1_mcart_1(esk2_0) != esk4_0
      | k2_mcart_1(esk2_0) != esk5_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

fof(c_0_19,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | X2 = k4_xboole_0(X2,k2_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X29,X30,X31] :
      ( ( r2_hidden(k1_mcart_1(X29),X30)
        | ~ r2_hidden(X29,k2_zfmisc_1(X30,X31)) )
      & ( r2_hidden(k2_mcart_1(X29),X31)
        | ~ r2_hidden(X29,k2_zfmisc_1(X30,X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X26,X27,X28] :
      ( ( r2_hidden(X26,X28)
        | ~ r1_tarski(k2_tarski(X26,X27),X28) )
      & ( r2_hidden(X27,X28)
        | ~ r1_tarski(k2_tarski(X26,X27),X28) )
      & ( ~ r2_hidden(X26,X28)
        | ~ r2_hidden(X27,X28)
        | r1_tarski(k2_tarski(X26,X27),X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_28,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_29,plain,(
    ! [X32,X33,X34,X35,X36] :
      ( ~ r2_hidden(k1_mcart_1(X32),X33)
      | ~ r2_hidden(k2_mcart_1(X32),X34)
      | X32 != k4_tarski(X35,X36)
      | r2_hidden(X32,k2_zfmisc_1(X33,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_mcart_1])])])).

fof(c_0_30,plain,(
    ! [X43,X44] :
      ( k1_mcart_1(k4_tarski(X43,X44)) = X43
      & k2_mcart_1(k4_tarski(X43,X44)) = X44 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( X2 = k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X3))
    | r2_hidden(X3,X2)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_33,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X40,X41,X42] :
      ( ( r2_hidden(k1_mcart_1(X40),X41)
        | ~ r2_hidden(X40,k2_zfmisc_1(X41,k1_tarski(X42))) )
      & ( k2_mcart_1(X40) = X42
        | ~ r2_hidden(X40,k2_zfmisc_1(X41,k1_tarski(X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_mcart_1])])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(k2_mcart_1(X1),X3)
    | X1 != k4_tarski(X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X4,k2_enumset1(X1,X1,X1,X3))
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_22]),c_0_23])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( k2_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X37,X38,X39] :
      ( ( k1_mcart_1(X37) = X38
        | ~ r2_hidden(X37,k2_zfmisc_1(k1_tarski(X38),X39)) )
      & ( r2_hidden(k2_mcart_1(X37),X39)
        | ~ r2_hidden(X37,k2_zfmisc_1(k1_tarski(X38),X39)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).

cnf(c_0_47,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk4_0,X1)
    | r2_hidden(esk3_0,X1)
    | ~ r2_hidden(k1_mcart_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( k2_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_26]),c_0_22]),c_0_23])).

cnf(c_0_51,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_mcart_1(esk2_0)),k2_zfmisc_1(X2,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1))
    | r2_hidden(esk4_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk4_0
    | k2_mcart_1(esk2_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_55,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_34])).

cnf(c_0_56,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_26]),c_0_22]),c_0_23])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,k1_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)))
    | r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_39]),c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk3_0
    | k2_mcart_1(esk2_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,k1_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_55])])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_61]),c_0_39]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n007.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 16:26:51 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.18/0.48  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.18/0.48  # and selection function SelectNegativeLiterals.
% 0.18/0.48  #
% 0.18/0.48  # Preprocessing time       : 0.028 s
% 0.18/0.48  # Presaturation interreduction done
% 0.18/0.48  
% 0.18/0.48  # Proof found!
% 0.18/0.48  # SZS status Theorem
% 0.18/0.48  # SZS output start CNFRefutation
% 0.18/0.48  fof(t17_mcart_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&k2_mcart_1(X1)=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_mcart_1)).
% 0.18/0.48  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.18/0.48  fof(t144_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 0.18/0.48  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.48  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.48  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.48  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.18/0.48  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.18/0.48  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.48  fof(t11_mcart_1, axiom, ![X1, X2, X3]:((r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))=>(![X4, X5]:X1!=k4_tarski(X4,X5)|r2_hidden(X1,k2_zfmisc_1(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_mcart_1)).
% 0.18/0.48  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.18/0.48  fof(t13_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))=>(r2_hidden(k1_mcart_1(X1),X2)&k2_mcart_1(X1)=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 0.18/0.48  fof(t12_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 0.18/0.48  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4)))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&k2_mcart_1(X1)=X4))), inference(assume_negation,[status(cth)],[t17_mcart_1])).
% 0.18/0.48  fof(c_0_14, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.18/0.48  fof(c_0_15, plain, ![X23, X24, X25]:(r2_hidden(X23,X25)|r2_hidden(X24,X25)|X25=k4_xboole_0(X25,k2_tarski(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).
% 0.18/0.48  fof(c_0_16, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.48  fof(c_0_17, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.48  fof(c_0_18, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0)))&((k1_mcart_1(esk2_0)!=esk3_0|k2_mcart_1(esk2_0)!=esk5_0)&(k1_mcart_1(esk2_0)!=esk4_0|k2_mcart_1(esk2_0)!=esk5_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 0.18/0.48  fof(c_0_19, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.48  cnf(c_0_20, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.48  cnf(c_0_21, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|X2=k4_xboole_0(X2,k2_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.48  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.48  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.48  fof(c_0_24, plain, ![X29, X30, X31]:((r2_hidden(k1_mcart_1(X29),X30)|~r2_hidden(X29,k2_zfmisc_1(X30,X31)))&(r2_hidden(k2_mcart_1(X29),X31)|~r2_hidden(X29,k2_zfmisc_1(X30,X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.18/0.48  cnf(c_0_25, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.48  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.48  fof(c_0_27, plain, ![X26, X27, X28]:(((r2_hidden(X26,X28)|~r1_tarski(k2_tarski(X26,X27),X28))&(r2_hidden(X27,X28)|~r1_tarski(k2_tarski(X26,X27),X28)))&(~r2_hidden(X26,X28)|~r2_hidden(X27,X28)|r1_tarski(k2_tarski(X26,X27),X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.18/0.48  fof(c_0_28, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.48  fof(c_0_29, plain, ![X32, X33, X34, X35, X36]:(~r2_hidden(k1_mcart_1(X32),X33)|~r2_hidden(k2_mcart_1(X32),X34)|(X32!=k4_tarski(X35,X36)|r2_hidden(X32,k2_zfmisc_1(X33,X34)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_mcart_1])])])).
% 0.18/0.48  fof(c_0_30, plain, ![X43, X44]:(k1_mcart_1(k4_tarski(X43,X44))=X43&k2_mcart_1(k4_tarski(X43,X44))=X44), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.18/0.48  cnf(c_0_31, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_20])).
% 0.18/0.48  cnf(c_0_32, plain, (X2=k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X3))|r2_hidden(X3,X2)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.18/0.48  cnf(c_0_33, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.48  cnf(c_0_34, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.18/0.48  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.48  cnf(c_0_36, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.48  fof(c_0_37, plain, ![X40, X41, X42]:((r2_hidden(k1_mcart_1(X40),X41)|~r2_hidden(X40,k2_zfmisc_1(X41,k1_tarski(X42))))&(k2_mcart_1(X40)=X42|~r2_hidden(X40,k2_zfmisc_1(X41,k1_tarski(X42))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_mcart_1])])])).
% 0.18/0.48  cnf(c_0_38, plain, (r2_hidden(X1,k2_zfmisc_1(X2,X3))|~r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(k2_mcart_1(X1),X3)|X1!=k4_tarski(X4,X5)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.48  cnf(c_0_39, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.48  cnf(c_0_40, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.48  cnf(c_0_41, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|~r2_hidden(X4,k2_enumset1(X1,X1,X1,X3))|~r2_hidden(X4,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.18/0.48  cnf(c_0_42, negated_conjecture, (r2_hidden(k1_mcart_1(esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.48  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_22]), c_0_23])).
% 0.18/0.48  cnf(c_0_44, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_36])).
% 0.18/0.48  cnf(c_0_45, plain, (k2_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.48  fof(c_0_46, plain, ![X37, X38, X39]:((k1_mcart_1(X37)=X38|~r2_hidden(X37,k2_zfmisc_1(k1_tarski(X38),X39)))&(r2_hidden(k2_mcart_1(X37),X39)|~r2_hidden(X37,k2_zfmisc_1(k1_tarski(X38),X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).
% 0.18/0.48  cnf(c_0_47, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X1,X3)|~r2_hidden(X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_38]), c_0_39]), c_0_40])).
% 0.18/0.48  cnf(c_0_48, negated_conjecture, (r2_hidden(esk4_0,X1)|r2_hidden(esk3_0,X1)|~r2_hidden(k1_mcart_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.18/0.48  cnf(c_0_49, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.18/0.48  cnf(c_0_50, plain, (k2_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(X3,k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_26]), c_0_22]), c_0_23])).
% 0.18/0.48  cnf(c_0_51, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.48  cnf(c_0_52, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_mcart_1(esk2_0)),k2_zfmisc_1(X2,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_42])).
% 0.18/0.48  cnf(c_0_53, negated_conjecture, (r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1))|r2_hidden(esk4_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.18/0.48  cnf(c_0_54, negated_conjecture, (k1_mcart_1(esk2_0)!=esk4_0|k2_mcart_1(esk2_0)!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.48  cnf(c_0_55, negated_conjecture, (k2_mcart_1(esk2_0)=esk5_0), inference(spm,[status(thm)],[c_0_50, c_0_34])).
% 0.18/0.48  cnf(c_0_56, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_26]), c_0_22]), c_0_23])).
% 0.18/0.48  cnf(c_0_57, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,k1_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)))|r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.18/0.48  cnf(c_0_58, negated_conjecture, (k1_mcart_1(esk2_0)!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 0.18/0.48  cnf(c_0_59, negated_conjecture, (r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0)))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_39]), c_0_58])).
% 0.18/0.48  cnf(c_0_60, negated_conjecture, (k1_mcart_1(esk2_0)!=esk3_0|k2_mcart_1(esk2_0)!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.48  cnf(c_0_61, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,k1_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_52, c_0_59])).
% 0.18/0.48  cnf(c_0_62, negated_conjecture, (k1_mcart_1(esk2_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_55])])).
% 0.18/0.48  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_61]), c_0_39]), c_0_62]), ['proof']).
% 0.18/0.48  # SZS output end CNFRefutation
% 0.18/0.48  # Proof object total steps             : 64
% 0.18/0.48  # Proof object clause steps            : 37
% 0.18/0.48  # Proof object formula steps           : 27
% 0.18/0.48  # Proof object conjectures             : 18
% 0.18/0.48  # Proof object clause conjectures      : 15
% 0.18/0.48  # Proof object formula conjectures     : 3
% 0.18/0.48  # Proof object initial clauses used    : 16
% 0.18/0.48  # Proof object initial formulas used   : 13
% 0.18/0.48  # Proof object generating inferences   : 11
% 0.18/0.48  # Proof object simplifying inferences  : 28
% 0.18/0.48  # Training examples: 0 positive, 0 negative
% 0.18/0.48  # Parsed axioms                        : 13
% 0.18/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.48  # Initial clauses                      : 28
% 0.18/0.48  # Removed in clause preprocessing      : 3
% 0.18/0.48  # Initial clauses in saturation        : 25
% 0.18/0.48  # Processed clauses                    : 323
% 0.18/0.48  # ...of these trivial                  : 14
% 0.18/0.48  # ...subsumed                          : 84
% 0.18/0.48  # ...remaining for further processing  : 225
% 0.18/0.48  # Other redundant clauses eliminated   : 24
% 0.18/0.48  # Clauses deleted for lack of memory   : 0
% 0.18/0.48  # Backward-subsumed                    : 4
% 0.18/0.48  # Backward-rewritten                   : 69
% 0.18/0.48  # Generated clauses                    : 7541
% 0.18/0.48  # ...of the previous two non-trivial   : 7230
% 0.18/0.48  # Contextual simplify-reflections      : 0
% 0.18/0.48  # Paramodulations                      : 7517
% 0.18/0.48  # Factorizations                       : 0
% 0.18/0.48  # Equation resolutions                 : 24
% 0.18/0.48  # Propositional unsat checks           : 0
% 0.18/0.48  #    Propositional check models        : 0
% 0.18/0.48  #    Propositional check unsatisfiable : 0
% 0.18/0.48  #    Propositional clauses             : 0
% 0.18/0.48  #    Propositional clauses after purity: 0
% 0.18/0.48  #    Propositional unsat core size     : 0
% 0.18/0.48  #    Propositional preprocessing time  : 0.000
% 0.18/0.48  #    Propositional encoding time       : 0.000
% 0.18/0.48  #    Propositional solver time         : 0.000
% 0.18/0.48  #    Success case prop preproc time    : 0.000
% 0.18/0.48  #    Success case prop encoding time   : 0.000
% 0.18/0.48  #    Success case prop solver time     : 0.000
% 0.18/0.48  # Current number of processed clauses  : 124
% 0.18/0.48  #    Positive orientable unit clauses  : 35
% 0.18/0.48  #    Positive unorientable unit clauses: 1
% 0.18/0.48  #    Negative unit clauses             : 2
% 0.18/0.48  #    Non-unit-clauses                  : 86
% 0.18/0.48  # Current number of unprocessed clauses: 6866
% 0.18/0.48  # ...number of literals in the above   : 26997
% 0.18/0.48  # Current number of archived formulas  : 0
% 0.18/0.48  # Current number of archived clauses   : 98
% 0.18/0.48  # Clause-clause subsumption calls (NU) : 2038
% 0.18/0.48  # Rec. Clause-clause subsumption calls : 1753
% 0.18/0.48  # Non-unit clause-clause subsumptions  : 87
% 0.18/0.48  # Unit Clause-clause subsumption calls : 247
% 0.18/0.48  # Rewrite failures with RHS unbound    : 0
% 0.18/0.48  # BW rewrite match attempts            : 238
% 0.18/0.48  # BW rewrite match successes           : 67
% 0.18/0.48  # Condensation attempts                : 0
% 0.18/0.48  # Condensation successes               : 0
% 0.18/0.48  # Termbank termtop insertions          : 216201
% 0.18/0.48  
% 0.18/0.48  # -------------------------------------------------
% 0.18/0.48  # User time                : 0.152 s
% 0.18/0.48  # System time              : 0.008 s
% 0.18/0.48  # Total time               : 0.161 s
% 0.18/0.48  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
