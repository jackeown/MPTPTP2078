%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t50_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:09 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 170 expanded)
%              Number of clauses        :   22 (  73 expanded)
%              Number of leaves         :    5 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  102 ( 743 expanded)
%              Number of equality atoms :   93 ( 654 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k2_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t50_mcart_1.p',d2_mcart_1)).

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t50_mcart_1.p',t48_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t50_mcart_1.p',d3_mcart_1)).

fof(t50_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t50_mcart_1.p',t50_mcart_1)).

fof(d1_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k1_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t50_mcart_1.p',d1_mcart_1)).

fof(c_0_5,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26] :
      ( ( X23 != k2_mcart_1(X20)
        | X20 != k4_tarski(X24,X25)
        | X23 = X25
        | X20 != k4_tarski(X21,X22) )
      & ( X20 = k4_tarski(esk7_2(X20,X26),esk8_2(X20,X26))
        | X26 = k2_mcart_1(X20)
        | X20 != k4_tarski(X21,X22) )
      & ( X26 != esk8_2(X20,X26)
        | X26 = k2_mcart_1(X20)
        | X20 != k4_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_mcart_1])])])])])])).

fof(c_0_6,plain,(
    ! [X50,X51,X52,X53] :
      ( X50 = k1_xboole_0
      | X51 = k1_xboole_0
      | X52 = k1_xboole_0
      | ~ m1_subset_1(X53,k3_zfmisc_1(X50,X51,X52))
      | X53 = k3_mcart_1(k5_mcart_1(X50,X51,X52,X53),k6_mcart_1(X50,X51,X52,X53),k7_mcart_1(X50,X51,X52,X53)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_7,plain,(
    ! [X29,X30,X31] : k3_mcart_1(X29,X30,X31) = k4_tarski(k4_tarski(X29,X30),X31) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & ~ ! [X4] :
                ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
               => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                  & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                  & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_mcart_1])).

cnf(c_0_9,plain,
    ( X1 = X4
    | X1 != k2_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))
    & ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_mcart_1(k1_mcart_1(esk4_0))
      | k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_mcart_1(k1_mcart_1(esk4_0))
      | k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_mcart_1(esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_13,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17] :
      ( ( X14 != k1_mcart_1(X11)
        | X11 != k4_tarski(X15,X16)
        | X14 = X15
        | X11 != k4_tarski(X12,X13) )
      & ( X11 = k4_tarski(esk5_2(X11,X17),esk6_2(X11,X17))
        | X17 = k1_mcart_1(X11)
        | X11 != k4_tarski(X12,X13) )
      & ( X17 != esk5_2(X11,X17)
        | X17 = k1_mcart_1(X11)
        | X11 != k4_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_mcart_1])])])])])])).

cnf(c_0_14,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X4,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_9])])).

cnf(c_0_15,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( X1 = X3
    | X1 != k1_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)),k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) = esk4_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_23,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X3,X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).

cnf(c_0_24,negated_conjecture,
    ( k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = k2_mcart_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)),k2_mcart_1(esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k1_mcart_1(k1_mcart_1(esk4_0))
    | k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_mcart_1(k1_mcart_1(esk4_0))
    | k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_mcart_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) = k1_mcart_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk4_0)) != k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)
    | k2_mcart_1(k1_mcart_1(esk4_0)) != k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_24])])).

cnf(c_0_30,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk4_0)) = k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk4_0)) != k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_28]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
