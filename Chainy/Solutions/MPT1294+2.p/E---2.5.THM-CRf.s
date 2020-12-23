%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1294+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:04 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   24 (  48 expanded)
%              Number of clauses        :   13 (  19 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   54 ( 155 expanded)
%              Number of equality atoms :   33 ( 112 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    9 (   1 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tops_2)).

fof(t46_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ~ ( X2 != k1_xboole_0
          & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t46_setfam_1)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',involutiveness_k7_setfam_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',t4_subset_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',dt_k7_setfam_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( ~ ( X2 != k1_xboole_0
              & k7_setfam_1(X1,X2) = k1_xboole_0 )
          & ~ ( k7_setfam_1(X1,X2) != k1_xboole_0
              & X2 = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t10_tops_2])).

fof(c_0_6,plain,(
    ! [X280,X281] :
      ( ~ m1_subset_1(X281,k1_zfmisc_1(k1_zfmisc_1(X280)))
      | X281 = k1_xboole_0
      | k7_setfam_1(X280,X281) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_setfam_1])])).

fof(c_0_7,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & ( k7_setfam_1(esk1_0,esk2_0) != k1_xboole_0
      | esk2_0 != k1_xboole_0 )
    & ( esk2_0 = k1_xboole_0
      | esk2_0 != k1_xboole_0 )
    & ( k7_setfam_1(esk1_0,esk2_0) != k1_xboole_0
      | k7_setfam_1(esk1_0,esk2_0) = k1_xboole_0 )
    & ( esk2_0 = k1_xboole_0
      | k7_setfam_1(esk1_0,esk2_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X278,X279] :
      ( ~ m1_subset_1(X279,k1_zfmisc_1(k1_zfmisc_1(X278)))
      | k7_setfam_1(X278,k7_setfam_1(X278,X279)) = X279 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

fof(c_0_9,plain,(
    ! [X124] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X124)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_10,plain,(
    ! [X276,X277] :
      ( ~ m1_subset_1(X277,k1_zfmisc_1(k1_zfmisc_1(X276)))
      | m1_subset_1(k7_setfam_1(X276,X277),k1_zfmisc_1(k1_zfmisc_1(X276))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

cnf(c_0_11,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | k7_setfam_1(X2,X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | k7_setfam_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( k7_setfam_1(esk1_0,esk2_0) != k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_19,plain,
    ( k7_setfam_1(X1,k7_setfam_1(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( m1_subset_1(k7_setfam_1(X1,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k7_setfam_1(esk1_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18])])).

cnf(c_0_22,plain,
    ( k7_setfam_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_19]),c_0_20])])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
