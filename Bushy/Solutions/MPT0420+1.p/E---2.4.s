%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t52_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:18 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   21 (  70 expanded)
%              Number of clauses        :   12 (  25 expanded)
%              Number of leaves         :    4 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 ( 226 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t52_setfam_1.p',t51_setfam_1)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t52_setfam_1.p',involutiveness_k7_setfam_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t52_setfam_1.p',dt_k7_setfam_1)).

fof(t52_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( r1_tarski(k7_setfam_1(X1,X2),X3)
          <=> r1_tarski(X2,k7_setfam_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t52_setfam_1.p',t52_setfam_1)).

fof(c_0_4,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X24)))
      | ~ r1_tarski(k7_setfam_1(X24,X25),k7_setfam_1(X24,X26))
      | r1_tarski(X25,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_setfam_1])])])).

fof(c_0_5,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13)))
      | k7_setfam_1(X13,k7_setfam_1(X13,X14)) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

fof(c_0_6,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9)))
      | m1_subset_1(k7_setfam_1(X9,X10),k1_zfmisc_1(k1_zfmisc_1(X9))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( r1_tarski(k7_setfam_1(X1,X2),X3)
            <=> r1_tarski(X2,k7_setfam_1(X1,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_setfam_1])).

cnf(c_0_8,plain,
    ( r1_tarski(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ r1_tarski(k7_setfam_1(X2,X1),k7_setfam_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & ( ~ r1_tarski(k7_setfam_1(esk1_0,esk2_0),esk3_0)
      | ~ r1_tarski(esk2_0,k7_setfam_1(esk1_0,esk3_0)) )
    & ( r1_tarski(k7_setfam_1(esk1_0,esk2_0),esk3_0)
      | r1_tarski(esk2_0,k7_setfam_1(esk1_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,k7_setfam_1(X2,X3))
    | ~ r1_tarski(k7_setfam_1(X2,X1),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(k7_setfam_1(esk1_0,esk2_0),esk3_0)
    | r1_tarski(esk2_0,k7_setfam_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(k7_setfam_1(esk1_0,esk2_0),esk3_0)
    | ~ r1_tarski(esk2_0,k7_setfam_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk2_0,k7_setfam_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tarski(k7_setfam_1(esk1_0,esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17])])).

cnf(c_0_19,plain,
    ( r1_tarski(k7_setfam_1(X1,X2),X3)
    | ~ r1_tarski(X2,k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_17]),c_0_15]),c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
