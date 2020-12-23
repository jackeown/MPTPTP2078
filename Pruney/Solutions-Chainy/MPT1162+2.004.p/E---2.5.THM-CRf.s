%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:58 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 576 expanded)
%              Number of clauses        :   37 ( 181 expanded)
%              Number of leaves         :    5 ( 139 expanded)
%              Depth                    :   12
%              Number of atoms          :  252 (4347 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   31 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_orders_2(X1,X2,X3)
                   => r1_tarski(k3_orders_2(X1,X4,X2),k3_orders_2(X1,X4,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_orders_2)).

fof(dt_k3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(t7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                 => r2_hidden(X4,X3) ) )
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(t57_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,k3_orders_2(X1,X4,X3))
                  <=> ( r2_orders_2(X1,X2,X3)
                      & r2_hidden(X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(t29_orders_2,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r2_orders_2(X1,X2,X3)
                      & r2_orders_2(X1,X3,X4) )
                   => r2_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_orders_2)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( r2_orders_2(X1,X2,X3)
                     => r1_tarski(k3_orders_2(X1,X4,X2),k3_orders_2(X1,X4,X3)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t64_orders_2])).

fof(c_0_6,plain,(
    ! [X9,X10,X11] :
      ( v2_struct_0(X9)
      | ~ v3_orders_2(X9)
      | ~ v4_orders_2(X9)
      | ~ v5_orders_2(X9)
      | ~ l1_orders_2(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | m1_subset_1(k3_orders_2(X9,X10,X11),k1_zfmisc_1(u1_struct_0(X9))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & r2_orders_2(esk2_0,esk3_0,esk4_0)
    & ~ r1_tarski(k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X5,X6,X7] :
      ( ( m1_subset_1(esk1_3(X5,X6,X7),X5)
        | r1_tarski(X6,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) )
      & ( r2_hidden(esk1_3(X5,X6,X7),X6)
        | r1_tarski(X6,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) )
      & ( ~ r2_hidden(esk1_3(X5,X6,X7),X7)
        | r1_tarski(X6,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

cnf(c_0_9,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_19,plain,(
    ! [X16,X17,X18,X19] :
      ( ( r2_orders_2(X16,X17,X18)
        | ~ r2_hidden(X17,k3_orders_2(X16,X19,X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( r2_hidden(X17,X19)
        | ~ r2_hidden(X17,k3_orders_2(X16,X19,X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ r2_orders_2(X16,X17,X18)
        | ~ r2_hidden(X17,X19)
        | r2_hidden(X17,k3_orders_2(X16,X19,X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).

fof(c_0_20,plain,(
    ! [X12,X13,X14,X15] :
      ( ~ v4_orders_2(X12)
      | ~ v5_orders_2(X12)
      | ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ m1_subset_1(X15,u1_struct_0(X12))
      | ~ r2_orders_2(X12,X13,X14)
      | ~ r2_orders_2(X12,X14,X15)
      | r2_orders_2(X12,X13,X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_orders_2])])])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,X2))
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,k3_orders_2(esk2_0,esk5_0,X2)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,X2))
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,k3_orders_2(esk2_0,esk5_0,X2)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(X2,k3_orders_2(X1,X4,X3))
    | v2_struct_0(X1)
    | ~ r2_orders_2(X1,X2,X3)
    | ~ r2_hidden(X2,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r2_orders_2(X1,X2,X4)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,X2))
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,X2)),k3_orders_2(esk2_0,esk5_0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,X2))
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,X2)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_28,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,X2))
    | ~ r2_orders_2(esk2_0,X1,X2)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( r2_orders_2(esk2_0,X1,esk4_0)
    | ~ r2_orders_2(esk2_0,X2,esk4_0)
    | ~ r2_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_31,negated_conjecture,
    ( r2_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,esk4_0))
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,esk4_0)),k3_orders_2(esk2_0,esk5_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,esk4_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,X2))
    | ~ r2_orders_2(esk2_0,esk1_3(X3,X1,k3_orders_2(esk2_0,esk5_0,X2)),X2)
    | ~ r2_hidden(esk1_3(X3,X1,k3_orders_2(esk2_0,esk5_0,X2)),esk5_0)
    | ~ m1_subset_1(esk1_3(X3,X1,k3_orders_2(esk2_0,esk5_0,X2)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k3_orders_2(esk2_0,esk5_0,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r2_orders_2(esk2_0,X1,esk4_0)
    | ~ r2_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_38,plain,
    ( r2_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,k3_orders_2(X1,X4,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),k3_orders_2(esk2_0,esk5_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_32]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_32]),c_0_34])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,k3_orders_2(X3,X2,X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,esk4_0))
    | ~ r2_orders_2(esk2_0,esk1_3(X2,X1,k3_orders_2(esk2_0,esk5_0,esk4_0)),esk3_0)
    | ~ r2_hidden(esk1_3(X2,X1,k3_orders_2(esk2_0,esk5_0,esk4_0)),esk5_0)
    | ~ m1_subset_1(esk1_3(X2,X1,k3_orders_2(esk2_0,esk5_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk4_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_25])])).

cnf(c_0_43,negated_conjecture,
    ( r2_orders_2(esk2_0,esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_10]),c_0_32]),c_0_40])]),c_0_15])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_39]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_10]),c_0_32]),c_0_40])]),c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( ~ m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_40])]),c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( ~ m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_17]),c_0_25])])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_17]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t64_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_orders_2(X1,X2,X3)=>r1_tarski(k3_orders_2(X1,X4,X2),k3_orders_2(X1,X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_orders_2)).
% 0.13/0.38  fof(dt_k3_orders_2, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 0.13/0.38  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 0.13/0.38  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 0.13/0.38  fof(t29_orders_2, axiom, ![X1]:(((v4_orders_2(X1)&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_orders_2(X1,X2,X3)&r2_orders_2(X1,X3,X4))=>r2_orders_2(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_orders_2)).
% 0.13/0.38  fof(c_0_5, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_orders_2(X1,X2,X3)=>r1_tarski(k3_orders_2(X1,X4,X2),k3_orders_2(X1,X4,X3)))))))), inference(assume_negation,[status(cth)],[t64_orders_2])).
% 0.13/0.38  fof(c_0_6, plain, ![X9, X10, X11]:(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~m1_subset_1(X11,u1_struct_0(X9))|m1_subset_1(k3_orders_2(X9,X10,X11),k1_zfmisc_1(u1_struct_0(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).
% 0.13/0.38  fof(c_0_7, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(r2_orders_2(esk2_0,esk3_0,esk4_0)&~r1_tarski(k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.13/0.38  fof(c_0_8, plain, ![X5, X6, X7]:((m1_subset_1(esk1_3(X5,X6,X7),X5)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5)))&((r2_hidden(esk1_3(X5,X6,X7),X6)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5)))&(~r2_hidden(esk1_3(X5,X6,X7),X7)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 0.13/0.38  cnf(c_0_9, plain, (v2_struct_0(X1)|m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_11, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_12, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_16, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 0.13/0.38  cnf(c_0_18, plain, (m1_subset_1(esk1_3(X1,X2,X3),X1)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  fof(c_0_19, plain, ![X16, X17, X18, X19]:(((r2_orders_2(X16,X17,X18)|~r2_hidden(X17,k3_orders_2(X16,X19,X18))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v3_orders_2(X16)|~v4_orders_2(X16)|~v5_orders_2(X16)|~l1_orders_2(X16)))&(r2_hidden(X17,X19)|~r2_hidden(X17,k3_orders_2(X16,X19,X18))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v3_orders_2(X16)|~v4_orders_2(X16)|~v5_orders_2(X16)|~l1_orders_2(X16))))&(~r2_orders_2(X16,X17,X18)|~r2_hidden(X17,X19)|r2_hidden(X17,k3_orders_2(X16,X19,X18))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v3_orders_2(X16)|~v4_orders_2(X16)|~v5_orders_2(X16)|~l1_orders_2(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 0.13/0.38  fof(c_0_20, plain, ![X12, X13, X14, X15]:(~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)|(~m1_subset_1(X13,u1_struct_0(X12))|(~m1_subset_1(X14,u1_struct_0(X12))|(~m1_subset_1(X15,u1_struct_0(X12))|(~r2_orders_2(X12,X13,X14)|~r2_orders_2(X12,X14,X15)|r2_orders_2(X12,X13,X15)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_orders_2])])])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,X2))|r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,k3_orders_2(esk2_0,esk5_0,X2)),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,X2))|m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,k3_orders_2(esk2_0,esk5_0,X2)),u1_struct_0(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_18, c_0_17])).
% 0.13/0.38  cnf(c_0_23, plain, (r2_hidden(X2,k3_orders_2(X1,X4,X3))|v2_struct_0(X1)|~r2_orders_2(X1,X2,X3)|~r2_hidden(X2,X4)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_24, plain, (r2_orders_2(X1,X2,X4)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~r2_orders_2(X1,X2,X3)|~r2_orders_2(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (r1_tarski(k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,X2))|r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,X2)),k3_orders_2(esk2_0,esk5_0,X1))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_21, c_0_17])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (r1_tarski(k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,X2))|m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,X2)),u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_22, c_0_17])).
% 0.13/0.38  cnf(c_0_28, plain, (r1_tarski(X2,X3)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,X2))|~r2_orders_2(esk2_0,X1,X2)|~r2_hidden(X1,esk5_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (r2_orders_2(esk2_0,X1,esk4_0)|~r2_orders_2(esk2_0,X2,esk4_0)|~r2_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_11]), c_0_12]), c_0_13])])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (r2_orders_2(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (r1_tarski(k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,esk4_0))|r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,esk4_0)),k3_orders_2(esk2_0,esk5_0,X1))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_26, c_0_25])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (~r1_tarski(k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (r1_tarski(k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,esk4_0))|m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,X1),k3_orders_2(esk2_0,esk5_0,esk4_0)),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_27, c_0_25])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,X2))|~r2_orders_2(esk2_0,esk1_3(X3,X1,k3_orders_2(esk2_0,esk5_0,X2)),X2)|~r2_hidden(esk1_3(X3,X1,k3_orders_2(esk2_0,esk5_0,X2)),esk5_0)|~m1_subset_1(esk1_3(X3,X1,k3_orders_2(esk2_0,esk5_0,X2)),u1_struct_0(esk2_0))|~m1_subset_1(k3_orders_2(esk2_0,esk5_0,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (r2_orders_2(esk2_0,X1,esk4_0)|~r2_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.13/0.38  cnf(c_0_38, plain, (r2_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(X2,k3_orders_2(X1,X4,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),k3_orders_2(esk2_0,esk5_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_32]), c_0_34])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_32]), c_0_34])).
% 0.13/0.38  cnf(c_0_41, plain, (r2_hidden(X1,X2)|v2_struct_0(X3)|~r2_hidden(X1,k3_orders_2(X3,X2,X4))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,esk4_0))|~r2_orders_2(esk2_0,esk1_3(X2,X1,k3_orders_2(esk2_0,esk5_0,esk4_0)),esk3_0)|~r2_hidden(esk1_3(X2,X1,k3_orders_2(esk2_0,esk5_0,esk4_0)),esk5_0)|~m1_subset_1(esk1_3(X2,X1,k3_orders_2(esk2_0,esk5_0,esk4_0)),u1_struct_0(esk2_0))|~m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk4_0),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_25])])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (r2_orders_2(esk2_0,esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_10]), c_0_32]), c_0_40])]), c_0_15])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk5_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk4_0)),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_39]), c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_10]), c_0_32]), c_0_40])]), c_0_15])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (~m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_40])]), c_0_34])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (~m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_17]), c_0_25])])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_17]), c_0_32])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 48
% 0.13/0.38  # Proof object clause steps            : 37
% 0.13/0.38  # Proof object formula steps           : 11
% 0.13/0.38  # Proof object conjectures             : 32
% 0.13/0.38  # Proof object clause conjectures      : 29
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 18
% 0.13/0.38  # Proof object initial formulas used   : 5
% 0.13/0.38  # Proof object generating inferences   : 19
% 0.13/0.38  # Proof object simplifying inferences  : 48
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 5
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 18
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 18
% 0.13/0.38  # Processed clauses                    : 121
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 121
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 2
% 0.13/0.38  # Generated clauses                    : 475
% 0.13/0.38  # ...of the previous two non-trivial   : 470
% 0.13/0.38  # Contextual simplify-reflections      : 8
% 0.13/0.38  # Paramodulations                      : 475
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 101
% 0.13/0.38  #    Positive orientable unit clauses  : 13
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 85
% 0.13/0.38  # Current number of unprocessed clauses: 381
% 0.13/0.38  # ...number of literals in the above   : 1366
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 20
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 2729
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 1228
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 8
% 0.13/0.38  # Unit Clause-clause subsumption calls : 194
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 23
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 24329
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.045 s
% 0.13/0.39  # System time              : 0.003 s
% 0.13/0.39  # Total time               : 0.047 s
% 0.13/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
