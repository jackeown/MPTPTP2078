%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t52_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:10 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   26 (  68 expanded)
%              Number of clauses        :   17 (  30 expanded)
%              Number of leaves         :    4 (  17 expanded)
%              Depth                    :   13
%              Number of atoms          :   54 ( 149 expanded)
%              Number of equality atoms :    3 (  18 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ~ r1_xboole_0(k3_zfmisc_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
     => ( ~ r1_xboole_0(X1,X4)
        & ~ r1_xboole_0(X2,X5)
        & ~ r1_xboole_0(X3,X6) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t52_mcart_1.p',t52_mcart_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t52_mcart_1.p',symmetry_r1_xboole_0)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t52_mcart_1.p',d3_zfmisc_1)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t52_mcart_1.p',t127_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ~ r1_xboole_0(k3_zfmisc_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
       => ( ~ r1_xboole_0(X1,X4)
          & ~ r1_xboole_0(X2,X5)
          & ~ r1_xboole_0(X3,X6) ) ) ),
    inference(assume_negation,[status(cth)],[t52_mcart_1])).

fof(c_0_5,plain,(
    ! [X16,X17] :
      ( ~ r1_xboole_0(X16,X17)
      | r1_xboole_0(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_6,negated_conjecture,
    ( ~ r1_xboole_0(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    & ( r1_xboole_0(esk1_0,esk4_0)
      | r1_xboole_0(esk2_0,esk5_0)
      | r1_xboole_0(esk3_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X13,X14,X15] : k3_zfmisc_1(X13,X14,X15) = k2_zfmisc_1(k2_zfmisc_1(X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X18,X19,X20,X21] :
      ( ( ~ r1_xboole_0(X18,X19)
        | r1_xboole_0(k2_zfmisc_1(X18,X20),k2_zfmisc_1(X19,X21)) )
      & ( ~ r1_xboole_0(X20,X21)
        | r1_xboole_0(k2_zfmisc_1(X18,X20),k2_zfmisc_1(X19,X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

cnf(c_0_9,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk4_0)
    | r1_xboole_0(esk2_0,esk5_0)
    | r1_xboole_0(esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( ~ r1_xboole_0(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk6_0)
    | r1_xboole_0(esk2_0,esk5_0)
    | r1_xboole_0(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(X1,esk3_0),k2_zfmisc_1(X2,esk6_0))
    | r1_xboole_0(esk4_0,esk1_0)
    | r1_xboole_0(esk2_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk5_0)
    | r1_xboole_0(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_18,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(X2,esk5_0))
    | r1_xboole_0(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X1,esk2_0),X2),k2_zfmisc_1(k2_zfmisc_1(X3,esk5_0),X4))
    | r1_xboole_0(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_20])).

cnf(c_0_22,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_21])).

cnf(c_0_23,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(esk1_0,X1),k2_zfmisc_1(esk4_0,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_22])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(esk4_0,X3),X4)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_23])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
