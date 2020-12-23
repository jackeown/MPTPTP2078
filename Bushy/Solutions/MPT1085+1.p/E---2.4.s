%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : finset_1__t13_finset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:12 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   14 (  20 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  49 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_finset_1,conjecture,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,X2)
        & v1_finset_1(X2) )
     => v1_finset_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t13_finset_1.p',t13_finset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t13_finset_1.p',t3_subset)).

fof(cc2_finset_1,axiom,(
    ! [X1] :
      ( v1_finset_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_finset_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t13_finset_1.p',cc2_finset_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( r1_tarski(X1,X2)
          & v1_finset_1(X2) )
       => v1_finset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t13_finset_1])).

fof(c_0_4,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X25,k1_zfmisc_1(X26))
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | m1_subset_1(X25,k1_zfmisc_1(X26)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_5,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & v1_finset_1(esk2_0)
    & ~ v1_finset_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X27,X28] :
      ( ~ v1_finset_1(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | v1_finset_1(X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_finset_1])])])).

cnf(c_0_7,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_finset_1(X2)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v1_finset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( ~ v1_finset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])]),c_0_12]),
    [proof]).
%------------------------------------------------------------------------------
