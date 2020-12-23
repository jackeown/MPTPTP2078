%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0860+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:55 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 115 expanded)
%              Number of clauses        :   20 (  44 expanded)
%              Number of leaves         :    9 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   88 ( 215 expanded)
%              Number of equality atoms :   53 ( 131 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,k2_tarski(X3,X4)))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & ( k2_mcart_1(X1) = X3
          | k2_mcart_1(X1) = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT003+2.ax',d2_tarski)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(X1,k2_zfmisc_1(X2,k2_tarski(X3,X4)))
       => ( r2_hidden(k1_mcart_1(X1),X2)
          & ( k2_mcart_1(X1) = X3
            | k2_mcart_1(X1) = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_mcart_1])).

fof(c_0_10,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,k2_tarski(esk3_0,esk4_0)))
    & ( k2_mcart_1(esk1_0) != esk3_0
      | ~ r2_hidden(k1_mcart_1(esk1_0),esk2_0) )
    & ( k2_mcart_1(esk1_0) != esk4_0
      | ~ r2_hidden(k1_mcart_1(esk1_0),esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_11,plain,(
    ! [X802,X803] : k1_enumset1(X802,X802,X803) = k2_tarski(X802,X803) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X2473,X2474,X2475] : k2_enumset1(X2473,X2473,X2474,X2475) = k1_enumset1(X2473,X2474,X2475) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_13,plain,(
    ! [X2476,X2477,X2478,X2479] : k3_enumset1(X2476,X2476,X2477,X2478,X2479) = k2_enumset1(X2476,X2477,X2478,X2479) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_14,plain,(
    ! [X2724,X2725,X2726,X2727,X2728] : k4_enumset1(X2724,X2724,X2725,X2726,X2727,X2728) = k3_enumset1(X2724,X2725,X2726,X2727,X2728) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_15,plain,(
    ! [X2775,X2776,X2777,X2778,X2779,X2780] : k5_enumset1(X2775,X2775,X2776,X2777,X2778,X2779,X2780) = k4_enumset1(X2775,X2776,X2777,X2778,X2779,X2780) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_16,plain,(
    ! [X2846,X2847,X2848,X2849,X2850,X2851,X2852] : k6_enumset1(X2846,X2846,X2847,X2848,X2849,X2850,X2851,X2852) = k5_enumset1(X2846,X2847,X2848,X2849,X2850,X2851,X2852) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_17,plain,(
    ! [X120,X121,X122,X123,X124,X125,X126,X127] :
      ( ( ~ r2_hidden(X123,X122)
        | X123 = X120
        | X123 = X121
        | X122 != k2_tarski(X120,X121) )
      & ( X124 != X120
        | r2_hidden(X124,X122)
        | X122 != k2_tarski(X120,X121) )
      & ( X124 != X121
        | r2_hidden(X124,X122)
        | X122 != k2_tarski(X120,X121) )
      & ( esk17_3(X125,X126,X127) != X125
        | ~ r2_hidden(esk17_3(X125,X126,X127),X127)
        | X127 = k2_tarski(X125,X126) )
      & ( esk17_3(X125,X126,X127) != X126
        | ~ r2_hidden(esk17_3(X125,X126,X127),X127)
        | X127 = k2_tarski(X125,X126) )
      & ( r2_hidden(esk17_3(X125,X126,X127),X127)
        | esk17_3(X125,X126,X127) = X125
        | esk17_3(X125,X126,X127) = X126
        | X127 = k2_tarski(X125,X126) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_18,plain,(
    ! [X26,X27,X28] :
      ( ( r2_hidden(k1_mcart_1(X26),X27)
        | ~ r2_hidden(X26,k2_zfmisc_1(X27,X28)) )
      & ( r2_hidden(k2_mcart_1(X26),X28)
        | ~ r2_hidden(X26,k2_zfmisc_1(X27,X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,k2_tarski(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_29,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( k2_mcart_1(esk1_0) != esk3_0
    | ~ r2_hidden(k1_mcart_1(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k2_mcart_1(esk1_0) != esk4_0
    | ~ r2_hidden(k1_mcart_1(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk1_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( k2_mcart_1(esk1_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])])).

cnf(c_0_37,negated_conjecture,
    ( k2_mcart_1(esk1_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_32])])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
