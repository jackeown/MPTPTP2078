%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t158_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:32 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   28 (  73 expanded)
%              Number of clauses        :   21 (  29 expanded)
%              Number of leaves         :    3 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  174 ( 737 expanded)
%              Number of equality atoms :   26 ( 120 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( X4 = k5_partfun1(X1,X2,X3)
        <=> ! [X5] :
              ( r2_hidden(X5,X4)
            <=> ? [X6] :
                  ( v1_funct_1(X6)
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & X6 = X5
                  & v1_partfun1(X6,X1)
                  & r1_partfun1(X3,X6) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t158_funct_2.p',d7_partfun1)).

fof(t158_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
         => ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t158_funct_2.p',t158_funct_2)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t158_funct_2.p',cc1_funct_2)).

fof(c_0_3,plain,(
    ! [X13,X14,X15,X16,X17,X19,X20,X21,X23] :
      ( ( v1_funct_1(esk5_5(X13,X14,X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( m1_subset_1(esk5_5(X13,X14,X15,X16,X17),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | ~ r2_hidden(X17,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( esk5_5(X13,X14,X15,X16,X17) = X17
        | ~ r2_hidden(X17,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( v1_partfun1(esk5_5(X13,X14,X15,X16,X17),X13)
        | ~ r2_hidden(X17,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( r1_partfun1(X15,esk5_5(X13,X14,X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | X20 != X19
        | ~ v1_partfun1(X20,X13)
        | ~ r1_partfun1(X15,X20)
        | r2_hidden(X19,X16)
        | X16 != k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( ~ r2_hidden(esk6_4(X13,X14,X15,X21),X21)
        | ~ v1_funct_1(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | X23 != esk6_4(X13,X14,X15,X21)
        | ~ v1_partfun1(X23,X13)
        | ~ r1_partfun1(X15,X23)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( v1_funct_1(esk7_4(X13,X14,X15,X21))
        | r2_hidden(esk6_4(X13,X14,X15,X21),X21)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( m1_subset_1(esk7_4(X13,X14,X15,X21),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | r2_hidden(esk6_4(X13,X14,X15,X21),X21)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( esk7_4(X13,X14,X15,X21) = esk6_4(X13,X14,X15,X21)
        | r2_hidden(esk6_4(X13,X14,X15,X21),X21)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( v1_partfun1(esk7_4(X13,X14,X15,X21),X13)
        | r2_hidden(esk6_4(X13,X14,X15,X21),X21)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( r1_partfun1(X15,esk7_4(X13,X14,X15,X21))
        | r2_hidden(esk6_4(X13,X14,X15,X21),X21)
        | X21 = k5_partfun1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
           => ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t158_funct_2])).

cnf(c_0_5,plain,
    ( v1_funct_1(esk5_5(X1,X2,X3,X4,X5))
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( esk5_5(X1,X2,X3,X4,X5) = X5
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_7,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r2_hidden(esk4_0,k5_partfun1(esk1_0,esk2_0,esk3_0))
    & ( ~ v1_funct_1(esk4_0)
      | ~ v1_funct_2(esk4_0,esk1_0,esk2_0)
      | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_8,plain,(
    ! [X48,X49,X50] :
      ( ( v1_funct_1(X50)
        | ~ v1_funct_1(X50)
        | ~ v1_partfun1(X50,X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( v1_funct_2(X50,X48,X49)
        | ~ v1_funct_1(X50)
        | ~ v1_partfun1(X50,X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_9,plain,
    ( v1_funct_1(X1)
    | X2 != k5_partfun1(X3,X4,X5)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X5) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_10,plain,
    ( v1_partfun1(esk5_5(X1,X2,X3,X4,X5),X1)
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_11,negated_conjecture,
    ( ~ v1_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,esk1_0,esk2_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk4_0,k5_partfun1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( v1_partfun1(X1,X2)
    | X3 != k5_partfun1(X2,X4,X5)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X5) ),
    inference(spm,[status(thm)],[c_0_10,c_0_6])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk5_5(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_partfun1(esk4_0,esk1_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_21,plain,
    ( v1_partfun1(X1,X2)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X4 != k5_partfun1(X2,X3,X5)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X5) ),
    inference(spm,[status(thm)],[c_0_18,c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_partfun1(esk4_0,esk1_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])])).

cnf(c_0_24,negated_conjecture,
    ( v1_partfun1(esk4_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_14]),c_0_15]),c_0_16])]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
