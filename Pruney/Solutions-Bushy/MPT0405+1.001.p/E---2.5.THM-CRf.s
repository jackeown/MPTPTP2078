%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0405+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  42 expanded)
%              Number of clauses        :   15 (  19 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   84 ( 158 expanded)
%              Number of equality atoms :   19 (  33 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_setfam_1,conjecture,(
    ! [X1] : r1_setfam_1(k4_setfam_1(X1,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_setfam_1)).

fof(d6_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_setfam_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k6_subset_1(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_setfam_1)).

fof(d2_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X1)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & r1_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] : r1_setfam_1(k4_setfam_1(X1,X1),X1) ),
    inference(assume_negation,[status(cth)],[t31_setfam_1])).

fof(c_0_6,plain,(
    ! [X15,X16,X17,X18,X21,X22,X23,X24,X25,X26,X28,X29] :
      ( ( r2_hidden(esk3_4(X15,X16,X17,X18),X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k4_setfam_1(X15,X16) )
      & ( r2_hidden(esk4_4(X15,X16,X17,X18),X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k4_setfam_1(X15,X16) )
      & ( X18 = k6_subset_1(esk3_4(X15,X16,X17,X18),esk4_4(X15,X16,X17,X18))
        | ~ r2_hidden(X18,X17)
        | X17 != k4_setfam_1(X15,X16) )
      & ( ~ r2_hidden(X22,X15)
        | ~ r2_hidden(X23,X16)
        | X21 != k6_subset_1(X22,X23)
        | r2_hidden(X21,X17)
        | X17 != k4_setfam_1(X15,X16) )
      & ( ~ r2_hidden(esk5_3(X24,X25,X26),X26)
        | ~ r2_hidden(X28,X24)
        | ~ r2_hidden(X29,X25)
        | esk5_3(X24,X25,X26) != k6_subset_1(X28,X29)
        | X26 = k4_setfam_1(X24,X25) )
      & ( r2_hidden(esk6_3(X24,X25,X26),X24)
        | r2_hidden(esk5_3(X24,X25,X26),X26)
        | X26 = k4_setfam_1(X24,X25) )
      & ( r2_hidden(esk7_3(X24,X25,X26),X25)
        | r2_hidden(esk5_3(X24,X25,X26),X26)
        | X26 = k4_setfam_1(X24,X25) )
      & ( esk5_3(X24,X25,X26) = k6_subset_1(esk6_3(X24,X25,X26),esk7_3(X24,X25,X26))
        | r2_hidden(esk5_3(X24,X25,X26),X26)
        | X26 = k4_setfam_1(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_setfam_1])])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ r1_setfam_1(k4_setfam_1(esk8_0,esk8_0),esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X7,X8,X9,X11,X12,X14] :
      ( ( r2_hidden(esk1_3(X7,X8,X9),X8)
        | ~ r2_hidden(X9,X7)
        | ~ r1_setfam_1(X7,X8) )
      & ( r1_tarski(X9,esk1_3(X7,X8,X9))
        | ~ r2_hidden(X9,X7)
        | ~ r1_setfam_1(X7,X8) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_setfam_1(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r1_tarski(esk2_2(X11,X12),X14)
        | r1_setfam_1(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

fof(c_0_9,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X34,k1_zfmisc_1(X35))
        | r1_tarski(X34,X35) )
      & ( ~ r1_tarski(X34,X35)
        | m1_subset_1(X34,k1_zfmisc_1(X35)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_10,plain,(
    ! [X32,X33] : m1_subset_1(k6_subset_1(X32,X33),k1_zfmisc_1(X32)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

cnf(c_0_11,plain,
    ( X1 = k6_subset_1(esk3_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k4_setfam_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_setfam_1(k4_setfam_1(esk8_0,esk8_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k6_subset_1(esk3_4(X1,X2,k4_setfam_1(X1,X2),X3),esk4_4(X1,X2,k4_setfam_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k4_setfam_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk2_2(k4_setfam_1(esk8_0,esk8_0),esk8_0),k4_setfam_1(esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k4_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( r1_tarski(k6_subset_1(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k6_subset_1(esk3_4(esk8_0,esk8_0,k4_setfam_1(esk8_0,esk8_0),esk2_2(k4_setfam_1(esk8_0,esk8_0),esk8_0)),esk4_4(esk8_0,esk8_0,k4_setfam_1(esk8_0,esk8_0),esk2_2(k4_setfam_1(esk8_0,esk8_0),esk8_0))) = esk2_2(k4_setfam_1(esk8_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(esk3_4(X1,X2,k4_setfam_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k4_setfam_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r1_setfam_1(X3,X2)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(esk2_2(X3,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk2_2(k4_setfam_1(esk8_0,esk8_0),esk8_0),esk3_4(esk8_0,esk8_0,k4_setfam_1(esk8_0,esk8_0),esk2_2(k4_setfam_1(esk8_0,esk8_0),esk8_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk3_4(esk8_0,esk8_0,k4_setfam_1(esk8_0,esk8_0),esk2_2(k4_setfam_1(esk8_0,esk8_0),esk8_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),c_0_12]),
    [proof]).

%------------------------------------------------------------------------------
