%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relset_1__t17_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:07 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   22 (  33 expanded)
%              Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   54 (  96 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_relset_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X4) )
       => m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t17_relset_1.p',t17_relset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t17_relset_1.p',t1_xboole_1)).

fof(t119_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t17_relset_1.p',t119_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t17_relset_1.p',t3_subset)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
       => ( ( r1_tarski(X1,X2)
            & r1_tarski(X3,X4) )
         => m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ) ) ),
    inference(assume_negation,[status(cth)],[t17_relset_1])).

fof(c_0_5,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,X22)
      | ~ r1_tarski(X22,X23)
      | r1_tarski(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_6,plain,(
    ! [X15,X16,X17,X18] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_tarski(X17,X18)
      | r1_tarski(k2_zfmisc_1(X15,X17),k2_zfmisc_1(X16,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_zfmisc_1])])).

fof(c_0_7,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X26,k1_zfmisc_1(X27))
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | m1_subset_1(X26,k1_zfmisc_1(X27)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_8,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    & r1_tarski(esk1_0,esk2_0)
    & r1_tarski(esk3_0,esk4_0)
    & ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5))
    | ~ r1_tarski(X5,X3)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k2_zfmisc_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(esk3_0,X2)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
