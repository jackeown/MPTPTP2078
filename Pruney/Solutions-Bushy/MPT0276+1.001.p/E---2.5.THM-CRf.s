%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0276+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:20 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :   24 (  52 expanded)
%              Number of clauses        :   13 (  20 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 185 expanded)
%              Number of equality atoms :   39 ( 124 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t74_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k4_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X1)
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X2)
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(l38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    <=> ( ~ r2_hidden(X1,X3)
        & ( r2_hidden(X2,X3)
          | X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t73_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k4_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X1)
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X2)
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t74_zfmisc_1])).

fof(c_0_6,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_xboole_0
    & k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk1_0)
    & k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk2_0)
    & k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X9,X10,X11] :
      ( ( ~ r2_hidden(X9,X11)
        | k4_xboole_0(k2_tarski(X9,X10),X11) != k2_tarski(X9,X10) )
      & ( ~ r2_hidden(X10,X11)
        | k4_xboole_0(k2_tarski(X9,X10),X11) != k2_tarski(X9,X10) )
      & ( r2_hidden(X9,X11)
        | r2_hidden(X10,X11)
        | k4_xboole_0(k2_tarski(X9,X10),X11) = k2_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

fof(c_0_8,plain,(
    ! [X6,X7,X8] :
      ( ( ~ r2_hidden(X6,X8)
        | k4_xboole_0(k2_tarski(X6,X7),X8) != k1_tarski(X6) )
      & ( r2_hidden(X7,X8)
        | X6 = X7
        | k4_xboole_0(k2_tarski(X6,X7),X8) != k1_tarski(X6) )
      & ( ~ r2_hidden(X7,X8)
        | r2_hidden(X6,X8)
        | k4_xboole_0(k2_tarski(X6,X7),X8) = k1_tarski(X6) )
      & ( X6 != X7
        | r2_hidden(X6,X8)
        | k4_xboole_0(k2_tarski(X6,X7),X8) = k1_tarski(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).

cnf(c_0_9,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | k4_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X4,X5] : k2_tarski(X4,X5) = k2_tarski(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_12,plain,(
    ! [X12,X13,X14] :
      ( ( r2_hidden(X12,X14)
        | k4_xboole_0(k2_tarski(X12,X13),X14) != k1_xboole_0 )
      & ( r2_hidden(X13,X14)
        | k4_xboole_0(k2_tarski(X12,X13),X14) != k1_xboole_0 )
      & ( ~ r2_hidden(X12,X14)
        | ~ r2_hidden(X13,X14)
        | k4_xboole_0(k2_tarski(X12,X13),X14) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_zfmisc_1])])])).

cnf(c_0_13,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) = k1_tarski(X3)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r2_hidden(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( k4_xboole_0(k2_tarski(X1,X3),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X2)
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_19])]),c_0_22]),
    [proof]).

%------------------------------------------------------------------------------
