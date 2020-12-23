%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0418+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   25 (  96 expanded)
%              Number of clauses        :   16 (  36 expanded)
%              Number of leaves         :    4 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 380 expanded)
%              Number of equality atoms :   11 (  30 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))
          <=> r2_hidden(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))
            <=> r2_hidden(X3,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_setfam_1])).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(k3_subset_1(X5,X8),X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(X5))
        | X7 != k7_setfam_1(X5,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))) )
      & ( ~ r2_hidden(k3_subset_1(X5,X8),X6)
        | r2_hidden(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(X5))
        | X7 != k7_setfam_1(X5,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))) )
      & ( m1_subset_1(esk1_3(X5,X6,X7),k1_zfmisc_1(X5))
        | X7 = k7_setfam_1(X5,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))) )
      & ( ~ r2_hidden(esk1_3(X5,X6,X7),X7)
        | ~ r2_hidden(k3_subset_1(X5,esk1_3(X5,X6,X7)),X6)
        | X7 = k7_setfam_1(X5,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))) )
      & ( r2_hidden(esk1_3(X5,X6,X7),X7)
        | r2_hidden(k3_subset_1(X5,esk1_3(X5,X6,X7)),X6)
        | X7 = k7_setfam_1(X5,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_6,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X10)))
      | m1_subset_1(k7_setfam_1(X10,X11),k1_zfmisc_1(k1_zfmisc_1(X10))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_7,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ( ~ r2_hidden(k3_subset_1(esk2_0,esk4_0),k7_setfam_1(esk2_0,esk3_0))
      | ~ r2_hidden(esk4_0,esk3_0) )
    & ( r2_hidden(k3_subset_1(esk2_0,esk4_0),k7_setfam_1(esk2_0,esk3_0))
      | r2_hidden(esk4_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( r2_hidden(k3_subset_1(X3,X1),X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | X2 != k7_setfam_1(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(esk2_0,esk4_0),k7_setfam_1(esk2_0,esk3_0))
    | ~ r2_hidden(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_8]),c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12)))
      | k7_setfam_1(X12,k7_setfam_1(X12,X13)) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

cnf(c_0_14,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X4 != k7_setfam_1(X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k7_setfam_1(esk2_0,k7_setfam_1(esk2_0,esk3_0)))
    | ~ r2_hidden(esk4_0,esk3_0)
    | ~ m1_subset_1(k7_setfam_1(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_16,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | ~ r2_hidden(k3_subset_1(X2,X1),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk2_0,esk4_0),k7_setfam_1(esk2_0,esk3_0))
    | r2_hidden(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk3_0)
    | ~ m1_subset_1(k7_setfam_1(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk4_0,k7_setfam_1(esk2_0,k7_setfam_1(esk2_0,esk3_0)))
    | r2_hidden(esk4_0,esk3_0)
    | ~ m1_subset_1(k7_setfam_1(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_12])])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_9]),c_0_17])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk4_0,k7_setfam_1(esk2_0,k7_setfam_1(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_9]),c_0_17])]),c_0_22])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_16]),c_0_17])]),c_0_22]),
    [proof]).

%------------------------------------------------------------------------------
