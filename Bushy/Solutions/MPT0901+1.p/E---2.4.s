%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t61_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:11 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 304 expanded)
%              Number of clauses        :   26 ( 130 expanded)
%              Number of leaves         :    6 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  121 (1506 expanded)
%              Number of equality atoms :  112 (1362 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t61_mcart_1.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t61_mcart_1.p',d3_mcart_1)).

fof(d2_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k2_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t61_mcart_1.p',d2_mcart_1)).

fof(t60_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t61_mcart_1.p',t60_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/mcart_1__t61_mcart_1.p',t61_mcart_1)).

fof(d1_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k1_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t61_mcart_1.p',d1_mcart_1)).

fof(c_0_6,plain,(
    ! [X34,X35,X36,X37] : k4_mcart_1(X34,X35,X36,X37) = k4_tarski(k3_mcart_1(X34,X35,X36),X37) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_7,plain,(
    ! [X31,X32,X33] : k3_mcart_1(X31,X32,X33) = k4_tarski(k4_tarski(X31,X32),X33) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_8,plain,(
    ! [X22,X23,X24,X25,X26,X27,X28] :
      ( ( X25 != k2_mcart_1(X22)
        | X22 != k4_tarski(X26,X27)
        | X25 = X27
        | X22 != k4_tarski(X23,X24) )
      & ( X22 = k4_tarski(esk8_2(X22,X28),esk9_2(X22,X28))
        | X28 = k2_mcart_1(X22)
        | X22 != k4_tarski(X23,X24) )
      & ( X28 != esk9_2(X22,X28)
        | X28 = k2_mcart_1(X22)
        | X22 != k4_tarski(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_mcart_1])])])])])])).

fof(c_0_9,plain,(
    ! [X64,X65,X66,X67,X68] :
      ( X64 = k1_xboole_0
      | X65 = k1_xboole_0
      | X66 = k1_xboole_0
      | X67 = k1_xboole_0
      | ~ m1_subset_1(X68,k4_zfmisc_1(X64,X65,X66,X67))
      | X68 = k4_mcart_1(k8_mcart_1(X64,X65,X66,X67,X68),k9_mcart_1(X64,X65,X66,X67,X68),k10_mcart_1(X64,X65,X66,X67,X68),k11_mcart_1(X64,X65,X66,X67,X68)) ) ),
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
    ( esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & m1_subset_1(esk5_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))
    & ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))
      | k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))
      | k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_mcart_1(k1_mcart_1(esk5_0))
      | k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_mcart_1(esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_17,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19] :
      ( ( X16 != k1_mcart_1(X13)
        | X13 != k4_tarski(X17,X18)
        | X16 = X17
        | X13 != k4_tarski(X14,X15) )
      & ( X13 = k4_tarski(esk6_2(X13,X19),esk7_2(X13,X19))
        | X19 = k1_mcart_1(X13)
        | X13 != k4_tarski(X14,X15) )
      & ( X19 != esk6_2(X13,X19)
        | X19 = k1_mcart_1(X13)
        | X13 != k4_tarski(X14,X15) ) ) ),
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
    ( m1_subset_1(esk5_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
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
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)),k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)) = esk5_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_28,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X3,X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])])).

cnf(c_0_29,negated_conjecture,
    ( k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) = k2_mcart_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)),k2_mcart_1(esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))
    | k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0)))
    | k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_mcart_1(k1_mcart_1(esk5_0))
    | k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_mcart_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( k4_tarski(k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)) = k1_mcart_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0))) != k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)
    | k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0))) != k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)
    | k2_mcart_1(k1_mcart_1(esk5_0)) != k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_29])])).

cnf(c_0_35,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk5_0)) = k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0))) != k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)
    | k2_mcart_1(k1_mcart_1(k1_mcart_1(esk5_0))) != k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_37,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk5_0)) = k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_30]),c_0_37]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
