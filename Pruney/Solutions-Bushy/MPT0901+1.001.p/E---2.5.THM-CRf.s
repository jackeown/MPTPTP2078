%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0901+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:22 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 648 expanded)
%              Number of clauses        :   30 ( 280 expanded)
%              Number of leaves         :    6 ( 146 expanded)
%              Depth                    :   14
%              Number of atoms          :  125 (3178 expanded)
%              Number of equality atoms :  116 (2874 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d2_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k2_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_mcart_1)).

fof(t60_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

fof(t61_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => ( k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
                & k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
                & k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
                & k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

fof(d1_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k1_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_mcart_1)).

fof(c_0_6,plain,(
    ! [X27,X28,X29,X30] : k4_mcart_1(X27,X28,X29,X30) = k4_tarski(k3_mcart_1(X27,X28,X29),X30) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_7,plain,(
    ! [X24,X25,X26] : k3_mcart_1(X24,X25,X26) = k4_tarski(k4_tarski(X24,X25),X26) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_8,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21] :
      ( ( X18 != k2_mcart_1(X15)
        | X15 != k4_tarski(X19,X20)
        | X18 = X20
        | X15 != k4_tarski(X16,X17) )
      & ( X15 = k4_tarski(esk3_2(X15,X21),esk4_2(X15,X21))
        | X21 = k2_mcart_1(X15)
        | X15 != k4_tarski(X16,X17) )
      & ( X21 != esk4_2(X15,X21)
        | X21 = k2_mcart_1(X15)
        | X15 != k4_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_mcart_1])])])])])])).

fof(c_0_9,plain,(
    ! [X31,X32,X33,X34,X35] :
      ( X31 = k1_xboole_0
      | X32 = k1_xboole_0
      | X33 = k1_xboole_0
      | X34 = k1_xboole_0
      | ~ m1_subset_1(X35,k4_zfmisc_1(X31,X32,X33,X34))
      | X35 = k4_mcart_1(k8_mcart_1(X31,X32,X33,X34,X35),k9_mcart_1(X31,X32,X33,X34,X35),k10_mcart_1(X31,X32,X33,X34,X35),k11_mcart_1(X31,X32,X33,X34,X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_mcart_1])])])).

cnf(c_0_10,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & X4 != k1_xboole_0
          & ~ ! [X5] :
                ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
               => ( k8_mcart_1(X1,X2,X3,X4,X5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
                  & k9_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X5)))
                  & k10_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(k1_mcart_1(X5))
                  & k11_mcart_1(X1,X2,X3,X4,X5) = k2_mcart_1(X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t61_mcart_1])).

cnf(c_0_13,plain,
    ( X1 = X4
    | X1 != k2_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_16,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & esk7_0 != k1_xboole_0
    & esk8_0 != k1_xboole_0
    & m1_subset_1(esk9_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
    & ( k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k1_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0)))
      | k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0)))
      | k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_mcart_1(k1_mcart_1(esk9_0))
      | k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_mcart_1(esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_17,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12] :
      ( ( X9 != k1_mcart_1(X6)
        | X6 != k4_tarski(X10,X11)
        | X9 = X10
        | X6 != k4_tarski(X7,X8) )
      & ( X6 = k4_tarski(esk1_2(X6,X12),esk2_2(X6,X12))
        | X12 = k1_mcart_1(X6)
        | X6 != k4_tarski(X7,X8) )
      & ( X12 != esk1_2(X6,X12)
        | X12 = k1_mcart_1(X6)
        | X6 != k4_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_mcart_1])])])])])])).

cnf(c_0_18,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X4,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_13])])).

cnf(c_0_19,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5)),k10_mcart_1(X1,X2,X3,X4,X5)),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk9_0,k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( X1 = X3
    | X1 != k1_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)),k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)),k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) = esk9_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_28,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X3,X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])])).

cnf(c_0_29,negated_conjecture,
    ( k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) = k2_mcart_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)),k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)),k2_mcart_1(esk9_0)) = esk9_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( k4_tarski(k4_tarski(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)),k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) = k1_mcart_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_33,negated_conjecture,
    ( k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) = k2_mcart_1(k1_mcart_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_32])).

cnf(c_0_34,negated_conjecture,
    ( k4_tarski(k4_tarski(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)),k2_mcart_1(k1_mcart_1(esk9_0))) = k1_mcart_1(esk9_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_35,negated_conjecture,
    ( k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k1_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0)))
    | k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0)))
    | k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_mcart_1(k1_mcart_1(esk9_0))
    | k11_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_mcart_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( k4_tarski(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) = k1_mcart_1(k1_mcart_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k1_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0)))
    | k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0)))
    | k10_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_mcart_1(k1_mcart_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_29])])).

cnf(c_0_38,negated_conjecture,
    ( k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k1_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0)))
    | k9_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_33])])).

cnf(c_0_40,negated_conjecture,
    ( k4_tarski(k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0)))) = k1_mcart_1(k1_mcart_1(esk9_0)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( k8_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k1_mcart_1(k1_mcart_1(k1_mcart_1(esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_38])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_40]),c_0_41]),
    [proof]).

%------------------------------------------------------------------------------
