%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t31_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:17 EDT 2019

% Result     : Theorem 1.17s
% Output     : CNFRefutation 1.17s
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
    file('/export/starexec/sandbox/benchmark/setfam_1__t31_setfam_1.p',t31_setfam_1)).

fof(d6_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_setfam_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k6_subset_1(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t31_setfam_1.p',d6_setfam_1)).

fof(d2_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X1)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & r1_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t31_setfam_1.p',d2_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t31_setfam_1.p',t3_subset)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t31_setfam_1.p',dt_k6_subset_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] : r1_setfam_1(k4_setfam_1(X1,X1),X1) ),
    inference(assume_negation,[status(cth)],[t31_setfam_1])).

fof(c_0_6,plain,(
    ! [X18,X19,X20,X21,X24,X25,X26,X27,X28,X29,X31,X32] :
      ( ( r2_hidden(esk4_4(X18,X19,X20,X21),X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k4_setfam_1(X18,X19) )
      & ( r2_hidden(esk5_4(X18,X19,X20,X21),X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k4_setfam_1(X18,X19) )
      & ( X21 = k6_subset_1(esk4_4(X18,X19,X20,X21),esk5_4(X18,X19,X20,X21))
        | ~ r2_hidden(X21,X20)
        | X20 != k4_setfam_1(X18,X19) )
      & ( ~ r2_hidden(X25,X18)
        | ~ r2_hidden(X26,X19)
        | X24 != k6_subset_1(X25,X26)
        | r2_hidden(X24,X20)
        | X20 != k4_setfam_1(X18,X19) )
      & ( ~ r2_hidden(esk6_3(X27,X28,X29),X29)
        | ~ r2_hidden(X31,X27)
        | ~ r2_hidden(X32,X28)
        | esk6_3(X27,X28,X29) != k6_subset_1(X31,X32)
        | X29 = k4_setfam_1(X27,X28) )
      & ( r2_hidden(esk7_3(X27,X28,X29),X27)
        | r2_hidden(esk6_3(X27,X28,X29),X29)
        | X29 = k4_setfam_1(X27,X28) )
      & ( r2_hidden(esk8_3(X27,X28,X29),X28)
        | r2_hidden(esk6_3(X27,X28,X29),X29)
        | X29 = k4_setfam_1(X27,X28) )
      & ( esk6_3(X27,X28,X29) = k6_subset_1(esk7_3(X27,X28,X29),esk8_3(X27,X28,X29))
        | r2_hidden(esk6_3(X27,X28,X29),X29)
        | X29 = k4_setfam_1(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_setfam_1])])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ r1_setfam_1(k4_setfam_1(esk1_0,esk1_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X10,X11,X12,X14,X15,X17] :
      ( ( r2_hidden(esk2_3(X10,X11,X12),X11)
        | ~ r2_hidden(X12,X10)
        | ~ r1_setfam_1(X10,X11) )
      & ( r1_tarski(X12,esk2_3(X10,X11,X12))
        | ~ r2_hidden(X12,X10)
        | ~ r1_setfam_1(X10,X11) )
      & ( r2_hidden(esk3_2(X14,X15),X14)
        | r1_setfam_1(X14,X15) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r1_tarski(esk3_2(X14,X15),X17)
        | r1_setfam_1(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

fof(c_0_9,plain,(
    ! [X47,X48] :
      ( ( ~ m1_subset_1(X47,k1_zfmisc_1(X48))
        | r1_tarski(X47,X48) )
      & ( ~ r1_tarski(X47,X48)
        | m1_subset_1(X47,k1_zfmisc_1(X48)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_10,plain,(
    ! [X35,X36] : m1_subset_1(k6_subset_1(X35,X36),k1_zfmisc_1(X35)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

cnf(c_0_11,plain,
    ( X1 = k6_subset_1(esk4_4(X2,X3,X4,X1),esk5_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k4_setfam_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_setfam_1(k4_setfam_1(esk1_0,esk1_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
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
    ( k6_subset_1(esk4_4(X1,X2,k4_setfam_1(X1,X2),X3),esk5_4(X1,X2,k4_setfam_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k4_setfam_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk3_2(k4_setfam_1(esk1_0,esk1_0),esk1_0),k4_setfam_1(esk1_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k4_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( r1_tarski(k6_subset_1(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k6_subset_1(esk4_4(esk1_0,esk1_0,k4_setfam_1(esk1_0,esk1_0),esk3_2(k4_setfam_1(esk1_0,esk1_0),esk1_0)),esk5_4(esk1_0,esk1_0,k4_setfam_1(esk1_0,esk1_0),esk3_2(k4_setfam_1(esk1_0,esk1_0),esk1_0))) = esk3_2(k4_setfam_1(esk1_0,esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(esk4_4(X1,X2,k4_setfam_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k4_setfam_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r1_setfam_1(X3,X2)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(esk3_2(X3,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk3_2(k4_setfam_1(esk1_0,esk1_0),esk1_0),esk4_4(esk1_0,esk1_0,k4_setfam_1(esk1_0,esk1_0),esk3_2(k4_setfam_1(esk1_0,esk1_0),esk1_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_4(esk1_0,esk1_0,k4_setfam_1(esk1_0,esk1_0),esk3_2(k4_setfam_1(esk1_0,esk1_0),esk1_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),c_0_12]),
    [proof]).
%------------------------------------------------------------------------------
