%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0421+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:45 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   12 (  24 expanded)
%              Number of clauses        :    7 (   8 expanded)
%              Number of leaves         :    2 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  66 expanded)
%              Number of equality atoms :   12 (  33 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( k7_setfam_1(X1,X2) = k7_setfam_1(X1,X3)
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_setfam_1)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( k7_setfam_1(X1,X2) = k7_setfam_1(X1,X3)
             => X2 = X3 ) ) ) ),
    inference(assume_negation,[status(cth)],[t53_setfam_1])).

fof(c_0_3,plain,(
    ! [X1935,X1936] :
      ( ~ m1_subset_1(X1936,k1_zfmisc_1(k1_zfmisc_1(X1935)))
      | k7_setfam_1(X1935,k7_setfam_1(X1935,X1936)) = X1936 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

fof(c_0_4,negated_conjecture,
    ( m1_subset_1(esk109_0,k1_zfmisc_1(k1_zfmisc_1(esk108_0)))
    & m1_subset_1(esk110_0,k1_zfmisc_1(k1_zfmisc_1(esk108_0)))
    & k7_setfam_1(esk108_0,esk109_0) = k7_setfam_1(esk108_0,esk110_0)
    & esk109_0 != esk110_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( k7_setfam_1(esk108_0,esk109_0) = k7_setfam_1(esk108_0,esk110_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( m1_subset_1(esk109_0,k1_zfmisc_1(k1_zfmisc_1(esk108_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( k7_setfam_1(esk108_0,k7_setfam_1(esk108_0,esk110_0)) = esk109_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7])])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk110_0,k1_zfmisc_1(k1_zfmisc_1(esk108_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( esk109_0 != esk110_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_8]),c_0_9])]),c_0_10]),
    [proof]).
%------------------------------------------------------------------------------
