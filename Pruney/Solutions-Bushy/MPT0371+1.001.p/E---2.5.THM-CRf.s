%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0371+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:31 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   22 ( 118 expanded)
%              Number of clauses        :   17 (  43 expanded)
%              Number of leaves         :    2 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 649 expanded)
%              Number of equality atoms :   14 ( 105 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( ~ r2_hidden(X4,X2)
                <=> r2_hidden(X4,X3) ) )
           => X2 = k3_subset_1(X1,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_subset_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ( ~ r2_hidden(X4,X2)
                  <=> r2_hidden(X4,X3) ) )
             => X2 = k3_subset_1(X1,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_subset_1])).

fof(c_0_3,plain,(
    ! [X5,X6,X7] :
      ( ( m1_subset_1(esk1_3(X5,X6,X7),X5)
        | X6 = k3_subset_1(X5,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) )
      & ( ~ r2_hidden(esk1_3(X5,X6,X7),X6)
        | r2_hidden(esk1_3(X5,X6,X7),X7)
        | X6 = k3_subset_1(X5,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) )
      & ( r2_hidden(esk1_3(X5,X6,X7),X6)
        | ~ r2_hidden(esk1_3(X5,X6,X7),X7)
        | X6 = k3_subset_1(X5,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t51_subset_1])])])])])])).

fof(c_0_4,negated_conjecture,(
    ! [X12] :
      ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
      & ( r2_hidden(X12,esk3_0)
        | r2_hidden(X12,esk4_0)
        | ~ m1_subset_1(X12,esk2_0) )
      & ( ~ r2_hidden(X12,esk4_0)
        | ~ r2_hidden(X12,esk3_0)
        | ~ m1_subset_1(X12,esk2_0) )
      & esk3_0 != k3_subset_1(esk2_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])])])).

cnf(c_0_5,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X1)
    | X2 = k3_subset_1(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X2 = k3_subset_1(X1,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X2 = k3_subset_1(X1,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_9,negated_conjecture,
    ( X1 = k3_subset_1(esk2_0,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,X1,esk4_0),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( esk3_0 != k3_subset_1(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( X1 = k3_subset_1(esk2_0,esk4_0)
    | r2_hidden(esk1_3(esk2_0,X1,esk4_0),esk4_0)
    | ~ r2_hidden(esk1_3(esk2_0,X1,esk4_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( X1 = k3_subset_1(esk2_0,esk4_0)
    | r2_hidden(esk1_3(esk2_0,X1,esk4_0),X1)
    | ~ r2_hidden(esk1_3(esk2_0,X1,esk4_0),esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk3_0,esk4_0),esk4_0)
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_10]),c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk3_0,esk4_0),esk3_0)
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_10]),c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk3_0,esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18])])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_18]),c_0_15])]),
    [proof]).

%------------------------------------------------------------------------------
