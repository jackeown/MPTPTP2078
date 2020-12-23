%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t51_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:18 EDT 2019

% Result     : Theorem 224.93s
% Output     : CNFRefutation 224.93s
% Verified   : 
% Statistics : Number of formulae       :   36 (  74 expanded)
%              Number of clauses        :   23 (  30 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  127 ( 274 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t51_setfam_1.p',t51_setfam_1)).

fof(d8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( X3 = k7_setfam_1(X1,X2)
          <=> ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( r2_hidden(X4,X3)
                <=> r2_hidden(k3_subset_1(X1,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t51_setfam_1.p',d8_setfam_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t51_setfam_1.p',dt_k7_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t51_setfam_1.p',d3_tarski)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t51_setfam_1.p',t4_subset)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t51_setfam_1.p',involutiveness_k7_setfam_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))
             => r1_tarski(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_setfam_1])).

fof(c_0_7,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X19,X18)
        | r2_hidden(k3_subset_1(X16,X19),X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(X16))
        | X18 != k7_setfam_1(X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X16)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) )
      & ( ~ r2_hidden(k3_subset_1(X16,X19),X17)
        | r2_hidden(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(X16))
        | X18 != k7_setfam_1(X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X16)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) )
      & ( m1_subset_1(esk5_3(X16,X17,X18),k1_zfmisc_1(X16))
        | X18 = k7_setfam_1(X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X16)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) )
      & ( ~ r2_hidden(esk5_3(X16,X17,X18),X18)
        | ~ r2_hidden(k3_subset_1(X16,esk5_3(X16,X17,X18)),X17)
        | X18 = k7_setfam_1(X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X16)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) )
      & ( r2_hidden(esk5_3(X16,X17,X18),X18)
        | r2_hidden(k3_subset_1(X16,esk5_3(X16,X17,X18)),X17)
        | X18 = k7_setfam_1(X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X16)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_8,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23)))
      | m1_subset_1(k7_setfam_1(X23,X24),k1_zfmisc_1(k1_zfmisc_1(X23))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_9,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk4_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk4_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_10,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & r1_tarski(k7_setfam_1(esk1_0,esk2_0),k7_setfam_1(esk1_0,esk3_0))
    & ~ r1_tarski(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_11,plain,(
    ! [X39,X40,X41] :
      ( ~ r2_hidden(X39,X40)
      | ~ m1_subset_1(X40,k1_zfmisc_1(X41))
      | m1_subset_1(X39,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_12,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X4 != k7_setfam_1(X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(k7_setfam_1(esk1_0,esk2_0),k7_setfam_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(k3_subset_1(X3,X1),X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | X2 != k7_setfam_1(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(X29)))
      | k7_setfam_1(X29,k7_setfam_1(X29,X30)) = X30 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | ~ r2_hidden(k3_subset_1(X2,X1),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,k7_setfam_1(esk1_0,esk3_0))
    | ~ r2_hidden(X1,k7_setfam_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_16,c_0_17])]),c_0_13])).

cnf(c_0_22,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(X1,k7_setfam_1(X2,k7_setfam_1(esk1_0,esk3_0)))
    | ~ r2_hidden(k3_subset_1(X2,X1),k7_setfam_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k7_setfam_1(esk1_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,k7_setfam_1(esk1_0,k7_setfam_1(esk1_0,esk3_0)))
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(k7_setfam_1(esk1_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_23])]),c_0_26])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(k7_setfam_1(esk1_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_22]),c_0_28])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_13]),c_0_28])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r2_hidden(esk4_2(X1,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_33,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
