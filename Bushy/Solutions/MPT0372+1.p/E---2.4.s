%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : subset_1__t53_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:25 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   23 (  83 expanded)
%              Number of clauses        :   16 (  30 expanded)
%              Number of leaves         :    3 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 ( 475 expanded)
%              Number of equality atoms :   20 (  82 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ~ ( r2_hidden(X4,X2)
                  <=> r2_hidden(X4,X3) ) )
           => X2 = k3_subset_1(X1,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t53_subset_1.p',t53_subset_1)).

fof(t51_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                <=> ~ r2_hidden(X4,X3) ) )
           => X2 = k3_subset_1(X1,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t53_subset_1.p',t51_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t53_subset_1.p',involutiveness_k3_subset_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ~ ( r2_hidden(X4,X2)
                    <=> r2_hidden(X4,X3) ) )
             => X2 = k3_subset_1(X1,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t53_subset_1])).

fof(c_0_4,plain,(
    ! [X21,X22,X23] :
      ( ( m1_subset_1(esk5_3(X21,X22,X23),X21)
        | X22 = k3_subset_1(X21,X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(X21)) )
      & ( ~ r2_hidden(esk5_3(X21,X22,X23),X22)
        | r2_hidden(esk5_3(X21,X22,X23),X23)
        | X22 = k3_subset_1(X21,X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(X21)) )
      & ( r2_hidden(esk5_3(X21,X22,X23),X22)
        | ~ r2_hidden(esk5_3(X21,X22,X23),X23)
        | X22 = k3_subset_1(X21,X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t51_subset_1])])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X8] :
      ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
      & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
      & ( ~ r2_hidden(X8,esk2_0)
        | ~ r2_hidden(X8,esk3_0)
        | ~ m1_subset_1(X8,esk1_0) )
      & ( r2_hidden(X8,esk2_0)
        | r2_hidden(X8,esk3_0)
        | ~ m1_subset_1(X8,esk1_0) )
      & esk2_0 != k3_subset_1(esk1_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X3)
    | X2 = k3_subset_1(X1,X3)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( k3_subset_1(X1,X2) = esk3_0
    | r2_hidden(esk5_3(X1,esk3_0,X2),esk2_0)
    | r2_hidden(esk5_3(X1,esk3_0,X2),X2)
    | ~ m1_subset_1(esk5_3(X1,esk3_0,X2),esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_9,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),X1)
    | X2 = k3_subset_1(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( k3_subset_1(esk1_0,X1) = esk3_0
    | r2_hidden(esk5_3(esk1_0,esk3_0,X1),esk2_0)
    | r2_hidden(esk5_3(esk1_0,esk3_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | X2 = k3_subset_1(X1,X3)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( k3_subset_1(esk1_0,esk2_0) = esk3_0
    | r2_hidden(esk5_3(esk1_0,esk3_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( ~ r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( k3_subset_1(esk1_0,esk2_0) = esk3_0
    | r2_hidden(esk5_3(esk1_0,esk3_0,esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_12]),c_0_10])])).

fof(c_0_17,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | k3_subset_1(X17,k3_subset_1(X17,X18)) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_18,negated_conjecture,
    ( k3_subset_1(esk1_0,esk2_0) = esk3_0
    | ~ m1_subset_1(esk5_3(esk1_0,esk3_0,esk2_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_14])).

cnf(c_0_19,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( k3_subset_1(esk1_0,esk2_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_9]),c_0_12]),c_0_10])])).

cnf(c_0_21,negated_conjecture,
    ( esk2_0 != k3_subset_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_12])]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
