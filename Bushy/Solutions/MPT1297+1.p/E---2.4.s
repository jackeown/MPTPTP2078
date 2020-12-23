%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t13_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:35 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   20 (  56 expanded)
%              Number of clauses        :   11 (  19 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 ( 194 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_tops_2,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(X1),X2))
          <=> v1_finset_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t13_tops_2.p',t13_tops_2)).

fof(l13_tops_2,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(X1),X2))
           => v1_finset_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t13_tops_2.p',l13_tops_2)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t13_tops_2.p',involutiveness_k7_setfam_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t13_tops_2.p',dt_k7_setfam_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v1_finset_1(k7_setfam_1(u1_struct_0(X1),X2))
            <=> v1_finset_1(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t13_tops_2])).

fof(c_0_5,plain,(
    ! [X15,X16] :
      ( ~ l1_struct_0(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
      | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X15),X16))
      | v1_finset_1(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_tops_2])])])).

fof(c_0_6,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & ( ~ v1_finset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0))
      | ~ v1_finset_1(esk2_0) )
    & ( v1_finset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0))
      | v1_finset_1(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_7,plain,
    ( v1_finset_1(X2)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X1),X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_finset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0))
    | v1_finset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13)))
      | k7_setfam_1(X13,k7_setfam_1(X13,X14)) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

fof(c_0_12,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8)))
      | m1_subset_1(k7_setfam_1(X8,X9),k1_zfmisc_1(k1_zfmisc_1(X8))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

cnf(c_0_13,negated_conjecture,
    ( ~ v1_finset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0))
    | ~ v1_finset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( v1_finset_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10])])).

cnf(c_0_15,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( ~ v1_finset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14])])).

cnf(c_0_18,plain,
    ( v1_finset_1(k7_setfam_1(u1_struct_0(X1),X2))
    | ~ v1_finset_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_15]),c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_14]),c_0_9]),c_0_10])]),
    [proof]).
%------------------------------------------------------------------------------
