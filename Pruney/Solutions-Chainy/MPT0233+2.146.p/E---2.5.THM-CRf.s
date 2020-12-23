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
% DateTime   : Thu Dec  3 10:39:13 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 904 expanded)
%              Number of clauses        :   56 ( 364 expanded)
%              Number of leaves         :   12 ( 265 expanded)
%              Depth                    :   19
%              Number of atoms          :  204 (1766 expanded)
%              Number of equality atoms :  133 (1383 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
        & X1 != X3
        & X1 != X4 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(l38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    <=> ( ~ r2_hidden(X1,X3)
        & ( r2_hidden(X2,X3)
          | X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
          & X1 != X3
          & X1 != X4 ) ),
    inference(assume_negation,[status(cth)],[t28_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X16,X15)
        | X16 = X13
        | X16 = X14
        | X15 != k2_tarski(X13,X14) )
      & ( X17 != X13
        | r2_hidden(X17,X15)
        | X15 != k2_tarski(X13,X14) )
      & ( X17 != X14
        | r2_hidden(X17,X15)
        | X15 != k2_tarski(X13,X14) )
      & ( esk1_3(X18,X19,X20) != X18
        | ~ r2_hidden(esk1_3(X18,X19,X20),X20)
        | X20 = k2_tarski(X18,X19) )
      & ( esk1_3(X18,X19,X20) != X19
        | ~ r2_hidden(esk1_3(X18,X19,X20),X20)
        | X20 = k2_tarski(X18,X19) )
      & ( r2_hidden(esk1_3(X18,X19,X20),X20)
        | esk1_3(X18,X19,X20) = X18
        | esk1_3(X18,X19,X20) = X19
        | X20 = k2_tarski(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_14,plain,(
    ! [X23,X24] : k1_enumset1(X23,X23,X24) = k2_tarski(X23,X24) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X25,X26,X27] : k2_enumset1(X25,X25,X26,X27) = k1_enumset1(X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X28,X29,X30,X31] : k3_enumset1(X28,X28,X29,X30,X31) = k2_enumset1(X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_17,plain,(
    ! [X32,X33,X34,X35,X36] : k4_enumset1(X32,X32,X33,X34,X35,X36) = k3_enumset1(X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_18,plain,(
    ! [X40,X41,X42] :
      ( ( ~ r1_tarski(X40,k2_tarski(X41,X42))
        | X40 = k1_xboole_0
        | X40 = k1_tarski(X41)
        | X40 = k1_tarski(X42)
        | X40 = k2_tarski(X41,X42) )
      & ( X40 != k1_xboole_0
        | r1_tarski(X40,k2_tarski(X41,X42)) )
      & ( X40 != k1_tarski(X41)
        | r1_tarski(X40,k2_tarski(X41,X42)) )
      & ( X40 != k1_tarski(X42)
        | r1_tarski(X40,k2_tarski(X41,X42)) )
      & ( X40 != k2_tarski(X41,X42)
        | r1_tarski(X40,k2_tarski(X41,X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

fof(c_0_19,plain,(
    ! [X22] : k2_tarski(X22,X22) = k1_tarski(X22) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,negated_conjecture,
    ( r1_tarski(k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))
    & esk2_0 != esk4_0
    & esk2_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_21,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k4_enumset1(X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | X1 = k4_enumset1(X3,X3,X3,X3,X3,X3)
    | X1 = k4_enumset1(X2,X2,X2,X2,X2,X3)
    | X1 = k4_enumset1(X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k4_enumset1(X2,X2,X2,X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_27]),c_0_22]),c_0_22]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k4_enumset1(X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) = k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)
    | k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)
    | k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X2,X2,X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) = k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)
    | k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) = k1_xboole_0
    | X1 = esk5_0
    | ~ r2_hidden(X1,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).

cnf(c_0_38,negated_conjecture,
    ( esk2_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) = k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)
    | k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)
    | k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) = k1_xboole_0
    | X1 = esk5_0
    | X1 = esk4_0
    | ~ r2_hidden(X1,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( esk2_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_43,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k2_xboole_0(X11,X12) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k4_enumset1(X2,X2,X2,X2,X2,X3))
    | X1 != k4_enumset1(X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_27]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)
    | k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_37]),c_0_38]),c_0_42])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_47,plain,
    ( r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) = k1_xboole_0
    | X1 = esk4_0
    | ~ r2_hidden(X1,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_45])).

fof(c_0_49,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(k2_xboole_0(X8,X9),X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_50,plain,
    ( k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X2)) = k4_enumset1(X1,X1,X1,X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_37]),c_0_42])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_53,plain,(
    ! [X37,X38,X39] :
      ( ( ~ r2_hidden(X37,X39)
        | k4_xboole_0(k2_tarski(X37,X38),X39) != k1_tarski(X37) )
      & ( r2_hidden(X38,X39)
        | X37 = X38
        | k4_xboole_0(k2_tarski(X37,X38),X39) != k1_tarski(X37) )
      & ( ~ r2_hidden(X38,X39)
        | r2_hidden(X37,X39)
        | k4_xboole_0(k2_tarski(X37,X38),X39) = k1_tarski(X37) )
      & ( X37 != X38
        | r2_hidden(X37,X39)
        | k4_xboole_0(k2_tarski(X37,X38),X39) = k1_tarski(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k2_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( k2_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k4_enumset1(X2,X2,X2,X2,X2,X3))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X1,X3),X2) != k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X4,X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_22]),c_0_23]),c_0_24]),c_0_25])).

fof(c_0_61,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k4_enumset1(X2,X2,X2,X2,X2,X3))
    | X1 != k4_enumset1(X2,X2,X2,X2,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X3)
    | k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),X1)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_xboole_0,k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X3),X2) != k4_enumset1(X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_27]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,k4_enumset1(X2,X2,X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_60])])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,plain,
    ( r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),X3) = k4_enumset1(X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X3)
    | X1 != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_27]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X3,X3,X3,X3,X3,X1)) != k4_enumset1(X1,X1,X1,X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,plain,
    ( k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,plain,
    ( k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),X2) = k4_enumset1(X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k4_enumset1(X1,X1,X1,X1,X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_71])).

cnf(c_0_76,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk2_0,k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_78,negated_conjecture,
    ( esk2_0 = X1
    | esk2_0 = X2 ),
    inference(spm,[status(thm)],[c_0_33,c_0_77])).

cnf(c_0_79,negated_conjecture,
    ( esk2_0 = X1 ),
    inference(ef,[status(thm)],[c_0_78])).

cnf(c_0_80,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_79]),c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:32:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.42/0.59  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.42/0.59  # and selection function GSelectMinInfpos.
% 0.42/0.59  #
% 0.42/0.59  # Preprocessing time       : 0.027 s
% 0.42/0.59  # Presaturation interreduction done
% 0.42/0.59  
% 0.42/0.59  # Proof found!
% 0.42/0.59  # SZS status Theorem
% 0.42/0.59  # SZS output start CNFRefutation
% 0.42/0.59  fof(t28_zfmisc_1, conjecture, ![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 0.42/0.59  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.42/0.59  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.42/0.59  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.42/0.59  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.42/0.59  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.42/0.59  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 0.42/0.59  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.42/0.59  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.42/0.59  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.42/0.59  fof(l38_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)<=>(~(r2_hidden(X1,X3))&(r2_hidden(X2,X3)|X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 0.42/0.59  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.42/0.59  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4))), inference(assume_negation,[status(cth)],[t28_zfmisc_1])).
% 0.42/0.59  fof(c_0_13, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X16,X15)|(X16=X13|X16=X14)|X15!=k2_tarski(X13,X14))&((X17!=X13|r2_hidden(X17,X15)|X15!=k2_tarski(X13,X14))&(X17!=X14|r2_hidden(X17,X15)|X15!=k2_tarski(X13,X14))))&(((esk1_3(X18,X19,X20)!=X18|~r2_hidden(esk1_3(X18,X19,X20),X20)|X20=k2_tarski(X18,X19))&(esk1_3(X18,X19,X20)!=X19|~r2_hidden(esk1_3(X18,X19,X20),X20)|X20=k2_tarski(X18,X19)))&(r2_hidden(esk1_3(X18,X19,X20),X20)|(esk1_3(X18,X19,X20)=X18|esk1_3(X18,X19,X20)=X19)|X20=k2_tarski(X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.42/0.59  fof(c_0_14, plain, ![X23, X24]:k1_enumset1(X23,X23,X24)=k2_tarski(X23,X24), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.42/0.59  fof(c_0_15, plain, ![X25, X26, X27]:k2_enumset1(X25,X25,X26,X27)=k1_enumset1(X25,X26,X27), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.42/0.59  fof(c_0_16, plain, ![X28, X29, X30, X31]:k3_enumset1(X28,X28,X29,X30,X31)=k2_enumset1(X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.42/0.59  fof(c_0_17, plain, ![X32, X33, X34, X35, X36]:k4_enumset1(X32,X32,X33,X34,X35,X36)=k3_enumset1(X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.42/0.59  fof(c_0_18, plain, ![X40, X41, X42]:((~r1_tarski(X40,k2_tarski(X41,X42))|(X40=k1_xboole_0|X40=k1_tarski(X41)|X40=k1_tarski(X42)|X40=k2_tarski(X41,X42)))&((((X40!=k1_xboole_0|r1_tarski(X40,k2_tarski(X41,X42)))&(X40!=k1_tarski(X41)|r1_tarski(X40,k2_tarski(X41,X42))))&(X40!=k1_tarski(X42)|r1_tarski(X40,k2_tarski(X41,X42))))&(X40!=k2_tarski(X41,X42)|r1_tarski(X40,k2_tarski(X41,X42))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 0.42/0.59  fof(c_0_19, plain, ![X22]:k2_tarski(X22,X22)=k1_tarski(X22), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.42/0.59  fof(c_0_20, negated_conjecture, ((r1_tarski(k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))&esk2_0!=esk4_0)&esk2_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.42/0.59  cnf(c_0_21, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.42/0.59  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.42/0.59  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.42/0.59  cnf(c_0_24, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.42/0.59  cnf(c_0_25, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.42/0.59  cnf(c_0_26, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k2_tarski(X2,X3)|~r1_tarski(X1,k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.42/0.59  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.59  cnf(c_0_28, negated_conjecture, (r1_tarski(k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.42/0.59  cnf(c_0_29, plain, (X1=X4|X1=X3|X2!=k4_enumset1(X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 0.42/0.59  cnf(c_0_30, plain, (X1=k1_xboole_0|X1=k4_enumset1(X3,X3,X3,X3,X3,X3)|X1=k4_enumset1(X2,X2,X2,X2,X2,X3)|X1=k4_enumset1(X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k4_enumset1(X2,X2,X2,X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_27]), c_0_22]), c_0_22]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 0.42/0.59  cnf(c_0_31, negated_conjecture, (r1_tarski(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 0.42/0.59  cnf(c_0_32, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.42/0.59  cnf(c_0_33, plain, (X1=X2|X1=X3|~r2_hidden(X1,k4_enumset1(X3,X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_29])).
% 0.42/0.59  cnf(c_0_34, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)=k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)|k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)|k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.42/0.59  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X2,X2,X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 0.42/0.59  cnf(c_0_36, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)=k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)|k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)=k1_xboole_0|X1=esk5_0|~r2_hidden(X1,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.42/0.59  cnf(c_0_37, plain, (r2_hidden(X1,k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).
% 0.42/0.59  cnf(c_0_38, negated_conjecture, (esk2_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.42/0.59  cnf(c_0_39, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)=k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)|k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.42/0.59  cnf(c_0_40, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.42/0.59  cnf(c_0_41, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)|k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)=k1_xboole_0|X1=esk5_0|X1=esk4_0|~r2_hidden(X1,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_33, c_0_39])).
% 0.42/0.59  cnf(c_0_42, negated_conjecture, (esk2_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.42/0.59  fof(c_0_43, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k2_xboole_0(X11,X12)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.42/0.59  cnf(c_0_44, plain, (r1_tarski(X1,k4_enumset1(X2,X2,X2,X2,X2,X3))|X1!=k4_enumset1(X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_27]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 0.42/0.59  cnf(c_0_45, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)|k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_37]), c_0_38]), c_0_42])).
% 0.42/0.59  cnf(c_0_46, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.42/0.59  cnf(c_0_47, plain, (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_44])).
% 0.42/0.59  cnf(c_0_48, negated_conjecture, (k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)=k1_xboole_0|X1=esk4_0|~r2_hidden(X1,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_33, c_0_45])).
% 0.42/0.59  fof(c_0_49, plain, ![X8, X9, X10]:(~r1_tarski(k2_xboole_0(X8,X9),X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.42/0.59  cnf(c_0_50, plain, (k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X2))=k4_enumset1(X1,X1,X1,X1,X1,X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.42/0.59  cnf(c_0_51, negated_conjecture, (k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_37]), c_0_42])).
% 0.42/0.59  cnf(c_0_52, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.42/0.59  fof(c_0_53, plain, ![X37, X38, X39]:(((~r2_hidden(X37,X39)|k4_xboole_0(k2_tarski(X37,X38),X39)!=k1_tarski(X37))&(r2_hidden(X38,X39)|X37=X38|k4_xboole_0(k2_tarski(X37,X38),X39)!=k1_tarski(X37)))&((~r2_hidden(X38,X39)|r2_hidden(X37,X39)|k4_xboole_0(k2_tarski(X37,X38),X39)=k1_tarski(X37))&(X37!=X38|r2_hidden(X37,X39)|k4_xboole_0(k2_tarski(X37,X38),X39)=k1_tarski(X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).
% 0.42/0.59  cnf(c_0_54, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.42/0.59  cnf(c_0_55, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k2_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.42/0.59  cnf(c_0_56, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.42/0.59  cnf(c_0_57, negated_conjecture, (k2_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.42/0.59  cnf(c_0_58, plain, (r1_tarski(X1,k4_enumset1(X2,X2,X2,X2,X2,X3))|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 0.42/0.59  cnf(c_0_59, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X1,X3),X2)!=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.42/0.59  cnf(c_0_60, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X4,X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 0.42/0.59  fof(c_0_61, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.42/0.59  cnf(c_0_62, plain, (r1_tarski(X1,k4_enumset1(X2,X2,X2,X2,X2,X3))|X1!=k4_enumset1(X2,X2,X2,X2,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 0.42/0.59  cnf(c_0_63, plain, (r2_hidden(X1,X3)|k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.42/0.59  cnf(c_0_64, negated_conjecture, (r1_tarski(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),X1)|~r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.42/0.59  cnf(c_0_65, plain, (r1_tarski(k1_xboole_0,k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_58])).
% 0.42/0.59  cnf(c_0_66, plain, (k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X3),X2)!=k4_enumset1(X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_27]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 0.42/0.59  cnf(c_0_67, plain, (r2_hidden(X1,k4_enumset1(X2,X2,X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_60])])).
% 0.42/0.59  cnf(c_0_68, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.42/0.59  cnf(c_0_69, plain, (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_62])).
% 0.42/0.59  cnf(c_0_70, plain, (k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),X3)=k4_enumset1(X1,X1,X1,X1,X1,X1)|r2_hidden(X1,X3)|X1!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_27]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 0.42/0.59  cnf(c_0_71, negated_conjecture, (r1_tarski(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.42/0.59  cnf(c_0_72, plain, (k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X3,X3,X3,X3,X3,X1))!=k4_enumset1(X1,X1,X1,X1,X1,X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.42/0.59  cnf(c_0_73, plain, (k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k4_enumset1(X1,X1,X1,X1,X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.42/0.59  cnf(c_0_74, plain, (k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),X2)=k4_enumset1(X1,X1,X1,X1,X1,X1)|r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_70])).
% 0.42/0.59  cnf(c_0_75, negated_conjecture, (k4_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k4_enumset1(X1,X1,X1,X1,X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_71])).
% 0.42/0.59  cnf(c_0_76, plain, (k4_enumset1(X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.42/0.59  cnf(c_0_77, negated_conjecture, (r2_hidden(esk2_0,k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 0.42/0.59  cnf(c_0_78, negated_conjecture, (esk2_0=X1|esk2_0=X2), inference(spm,[status(thm)],[c_0_33, c_0_77])).
% 0.42/0.59  cnf(c_0_79, negated_conjecture, (esk2_0=X1), inference(ef,[status(thm)],[c_0_78])).
% 0.42/0.59  cnf(c_0_80, plain, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_79]), c_0_79]), ['proof']).
% 0.42/0.59  # SZS output end CNFRefutation
% 0.42/0.59  # Proof object total steps             : 81
% 0.42/0.59  # Proof object clause steps            : 56
% 0.42/0.59  # Proof object formula steps           : 25
% 0.42/0.59  # Proof object conjectures             : 21
% 0.42/0.59  # Proof object clause conjectures      : 18
% 0.42/0.59  # Proof object formula conjectures     : 3
% 0.42/0.59  # Proof object initial clauses used    : 20
% 0.42/0.59  # Proof object initial formulas used   : 12
% 0.42/0.59  # Proof object generating inferences   : 18
% 0.42/0.59  # Proof object simplifying inferences  : 93
% 0.42/0.59  # Training examples: 0 positive, 0 negative
% 0.42/0.59  # Parsed axioms                        : 12
% 0.42/0.59  # Removed by relevancy pruning/SinE    : 0
% 0.42/0.59  # Initial clauses                      : 27
% 0.42/0.59  # Removed in clause preprocessing      : 5
% 0.42/0.59  # Initial clauses in saturation        : 22
% 0.42/0.59  # Processed clauses                    : 711
% 0.42/0.59  # ...of these trivial                  : 24
% 0.42/0.59  # ...subsumed                          : 361
% 0.42/0.59  # ...remaining for further processing  : 326
% 0.42/0.59  # Other redundant clauses eliminated   : 282
% 0.42/0.59  # Clauses deleted for lack of memory   : 0
% 0.42/0.59  # Backward-subsumed                    : 138
% 0.42/0.59  # Backward-rewritten                   : 155
% 0.42/0.59  # Generated clauses                    : 7696
% 0.42/0.59  # ...of the previous two non-trivial   : 6820
% 0.42/0.59  # Contextual simplify-reflections      : 14
% 0.42/0.59  # Paramodulations                      : 7360
% 0.42/0.59  # Factorizations                       : 56
% 0.42/0.59  # Equation resolutions                 : 282
% 0.42/0.59  # Propositional unsat checks           : 0
% 0.42/0.59  #    Propositional check models        : 0
% 0.42/0.59  #    Propositional check unsatisfiable : 0
% 0.42/0.59  #    Propositional clauses             : 0
% 0.42/0.59  #    Propositional clauses after purity: 0
% 0.42/0.59  #    Propositional unsat core size     : 0
% 0.42/0.59  #    Propositional preprocessing time  : 0.000
% 0.42/0.59  #    Propositional encoding time       : 0.000
% 0.42/0.59  #    Propositional solver time         : 0.000
% 0.42/0.59  #    Success case prop preproc time    : 0.000
% 0.42/0.59  #    Success case prop encoding time   : 0.000
% 0.42/0.59  #    Success case prop solver time     : 0.000
% 0.42/0.59  # Current number of processed clauses  : 3
% 0.42/0.59  #    Positive orientable unit clauses  : 2
% 0.42/0.59  #    Positive unorientable unit clauses: 1
% 0.42/0.59  #    Negative unit clauses             : 0
% 0.42/0.59  #    Non-unit-clauses                  : 0
% 0.42/0.59  # Current number of unprocessed clauses: 5913
% 0.42/0.59  # ...number of literals in the above   : 43190
% 0.42/0.59  # Current number of archived formulas  : 0
% 0.42/0.59  # Current number of archived clauses   : 320
% 0.42/0.59  # Clause-clause subsumption calls (NU) : 4957
% 0.42/0.59  # Rec. Clause-clause subsumption calls : 1456
% 0.42/0.59  # Non-unit clause-clause subsumptions  : 401
% 0.42/0.59  # Unit Clause-clause subsumption calls : 266
% 0.42/0.59  # Rewrite failures with RHS unbound    : 3
% 0.42/0.59  # BW rewrite match attempts            : 166
% 0.42/0.59  # BW rewrite match successes           : 127
% 0.42/0.59  # Condensation attempts                : 0
% 0.42/0.59  # Condensation successes               : 0
% 0.42/0.59  # Termbank termtop insertions          : 180161
% 0.42/0.59  
% 0.42/0.59  # -------------------------------------------------
% 0.42/0.59  # User time                : 0.236 s
% 0.42/0.59  # System time              : 0.008 s
% 0.42/0.59  # Total time               : 0.245 s
% 0.42/0.59  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
