%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t10_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:35 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   21 (  58 expanded)
%              Number of clauses        :   12 (  22 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   54 ( 223 expanded)
%              Number of equality atoms :   33 ( 169 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_tops_2,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ~ ( X2 != k1_xboole_0
            & k7_setfam_1(X1,X2) = k1_xboole_0 )
        & ~ ( k7_setfam_1(X1,X2) != k1_xboole_0
            & X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t10_tops_2.p',t10_tops_2)).

fof(t46_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ~ ( X2 != k1_xboole_0
          & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t10_tops_2.p',t46_setfam_1)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t10_tops_2.p',involutiveness_k7_setfam_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t10_tops_2.p',dt_k7_setfam_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( ~ ( X2 != k1_xboole_0
              & k7_setfam_1(X1,X2) = k1_xboole_0 )
          & ~ ( k7_setfam_1(X1,X2) != k1_xboole_0
              & X2 = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t10_tops_2])).

fof(c_0_5,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20)))
      | X21 = k1_xboole_0
      | k7_setfam_1(X20,X21) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_setfam_1])])).

fof(c_0_6,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & ( k7_setfam_1(esk1_0,esk2_0) != k1_xboole_0
      | esk2_0 != k1_xboole_0 )
    & ( esk2_0 = k1_xboole_0
      | esk2_0 != k1_xboole_0 )
    & ( k7_setfam_1(esk1_0,esk2_0) != k1_xboole_0
      | k7_setfam_1(esk1_0,esk2_0) = k1_xboole_0 )
    & ( esk2_0 = k1_xboole_0
      | k7_setfam_1(esk1_0,esk2_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12)))
      | k7_setfam_1(X12,k7_setfam_1(X12,X13)) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

cnf(c_0_8,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | k7_setfam_1(X2,X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | k7_setfam_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8)))
      | m1_subset_1(k7_setfam_1(X8,X9),k1_zfmisc_1(k1_zfmisc_1(X8))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

cnf(c_0_13,negated_conjecture,
    ( k7_setfam_1(esk1_0,esk2_0) != k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_15,plain,
    ( k7_setfam_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k7_setfam_1(X1,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_11])])).

cnf(c_0_16,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k7_setfam_1(esk1_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14])])).

cnf(c_0_18,plain,
    ( k7_setfam_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_10,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
