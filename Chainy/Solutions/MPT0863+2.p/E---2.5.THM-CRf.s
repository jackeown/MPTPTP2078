%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0863+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:55 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 351 expanded)
%              Number of clauses        :   23 ( 128 expanded)
%              Number of leaves         :    9 ( 106 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 593 expanded)
%              Number of equality atoms :   66 ( 514 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t19_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k2_tarski(X4,X5)))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & ( k2_mcart_1(X1) = X4
          | k2_mcart_1(X1) = X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_mcart_1)).

fof(t15_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & r2_hidden(k2_mcart_1(X1),X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(t16_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,k2_tarski(X3,X4)))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & ( k2_mcart_1(X1) = X3
          | k2_mcart_1(X1) = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),k2_tarski(X4,X5)))
       => ( ( k1_mcart_1(X1) = X2
            | k1_mcart_1(X1) = X3 )
          & ( k2_mcart_1(X1) = X4
            | k2_mcart_1(X1) = X5 ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_mcart_1])).

fof(c_0_10,plain,(
    ! [X44,X45,X46,X47] :
      ( ( k1_mcart_1(X44) = X45
        | k1_mcart_1(X44) = X46
        | ~ r2_hidden(X44,k2_zfmisc_1(k2_tarski(X45,X46),X47)) )
      & ( r2_hidden(k2_mcart_1(X44),X47)
        | ~ r2_hidden(X44,k2_zfmisc_1(k2_tarski(X45,X46),X47)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_mcart_1])])])).

fof(c_0_11,plain,(
    ! [X815,X816] : k1_enumset1(X815,X815,X816) = k2_tarski(X815,X816) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X2486,X2487,X2488] : k2_enumset1(X2486,X2486,X2487,X2488) = k1_enumset1(X2486,X2487,X2488) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_13,plain,(
    ! [X2489,X2490,X2491,X2492] : k3_enumset1(X2489,X2489,X2490,X2491,X2492) = k2_enumset1(X2489,X2490,X2491,X2492) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_14,plain,(
    ! [X2737,X2738,X2739,X2740,X2741] : k4_enumset1(X2737,X2737,X2738,X2739,X2740,X2741) = k3_enumset1(X2737,X2738,X2739,X2740,X2741) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_15,plain,(
    ! [X2788,X2789,X2790,X2791,X2792,X2793] : k5_enumset1(X2788,X2788,X2789,X2790,X2791,X2792,X2793) = k4_enumset1(X2788,X2789,X2790,X2791,X2792,X2793) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_16,plain,(
    ! [X2859,X2860,X2861,X2862,X2863,X2864,X2865] : k6_enumset1(X2859,X2859,X2860,X2861,X2862,X2863,X2864,X2865) = k5_enumset1(X2859,X2860,X2861,X2862,X2863,X2864,X2865) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_17,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0)))
    & ( k2_mcart_1(esk1_0) != esk4_0
      | k1_mcart_1(esk1_0) != esk2_0 )
    & ( k2_mcart_1(esk1_0) != esk5_0
      | k1_mcart_1(esk1_0) != esk2_0 )
    & ( k2_mcart_1(esk1_0) != esk4_0
      | k1_mcart_1(esk1_0) != esk3_0 )
    & ( k2_mcart_1(esk1_0) != esk5_0
      | k1_mcart_1(esk1_0) != esk3_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_18,plain,(
    ! [X48,X49,X50,X51] :
      ( ( r2_hidden(k1_mcart_1(X48),X49)
        | ~ r2_hidden(X48,k2_zfmisc_1(X49,k2_tarski(X50,X51))) )
      & ( k2_mcart_1(X48) = X50
        | k2_mcart_1(X48) = X51
        | ~ r2_hidden(X48,k2_zfmisc_1(X49,k2_tarski(X50,X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_mcart_1])])])).

cnf(c_0_19,plain,
    ( k1_mcart_1(X1) = X2
    | k1_mcart_1(X1) = X3
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4)) ),
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

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k2_mcart_1(X1) = X2
    | k2_mcart_1(X1) = X3
    | ~ r2_hidden(X1,k2_zfmisc_1(X4,k2_tarski(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k1_mcart_1(X1) = X3
    | k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_30,plain,
    ( k2_mcart_1(X1) = X3
    | k2_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(X4,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k2_mcart_1(esk1_0) != esk4_0
    | k1_mcart_1(esk1_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( k1_mcart_1(esk1_0) = esk2_0
    | k1_mcart_1(esk1_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k2_mcart_1(esk1_0) != esk4_0
    | k1_mcart_1(esk1_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( k2_mcart_1(esk1_0) = esk4_0
    | k2_mcart_1(esk1_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k2_mcart_1(esk1_0) != esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( k2_mcart_1(esk1_0) != esk5_0
    | k1_mcart_1(esk1_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( k2_mcart_1(esk1_0) = esk5_0 ),
    inference(sr,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( k2_mcart_1(esk1_0) != esk5_0
    | k1_mcart_1(esk1_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( k1_mcart_1(esk1_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_40,negated_conjecture,
    ( k1_mcart_1(esk1_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_37])])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_32,c_0_39]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
