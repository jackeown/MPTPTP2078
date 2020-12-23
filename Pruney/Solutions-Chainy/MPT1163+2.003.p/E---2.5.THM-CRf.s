%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:58 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 618 expanded)
%              Number of clauses        :   50 ( 199 expanded)
%              Number of leaves         :    6 ( 149 expanded)
%              Depth                    :   15
%              Number of atoms          :  262 (4554 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   31 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r1_tarski(X3,X4)
                   => r1_tarski(k3_orders_2(X1,X3,X2),k3_orders_2(X1,X4,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( r1_tarski(X3,X4)
                     => r1_tarski(k3_orders_2(X1,X3,X2),k3_orders_2(X1,X4,X2)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t65_orders_2])).

fof(c_0_7,plain,(
    ! [X8,X9,X10] :
      ( ( m1_subset_1(esk1_3(X8,X9,X10),X8)
        | r1_tarski(X9,X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) )
      & ( r2_hidden(esk1_3(X8,X9,X10),X9)
        | r1_tarski(X9,X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) )
      & ( ~ r2_hidden(esk1_3(X8,X9,X10),X10)
        | r1_tarski(X9,X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & r1_tarski(esk4_0,esk5_0)
    & ~ r1_tarski(k3_orders_2(esk2_0,esk4_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ v3_orders_2(X14)
      | ~ v4_orders_2(X14)
      | ~ v5_orders_2(X14)
      | ~ l1_orders_2(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | m1_subset_1(k3_orders_2(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X14))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).

fof(c_0_10,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X12,k1_zfmisc_1(X13))
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | m1_subset_1(X12,k1_zfmisc_1(X13)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_21,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ r2_hidden(X7,X6)
      | r2_hidden(X7,X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,esk5_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,esk5_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_12])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_29,plain,(
    ! [X17,X18,X19,X20] :
      ( ( r2_orders_2(X17,X18,X19)
        | ~ r2_hidden(X18,k3_orders_2(X17,X20,X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r2_hidden(X18,X20)
        | ~ r2_hidden(X18,k3_orders_2(X17,X20,X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r2_orders_2(X17,X18,X19)
        | ~ r2_hidden(X18,X20)
        | r2_hidden(X18,k3_orders_2(X17,X20,X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk2_0,esk4_0,X1),esk5_0)
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,X1),esk5_0),k3_orders_2(esk2_0,esk4_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk2_0,esk4_0,X1),esk5_0)
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,X1),esk5_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk2_0,esk4_0,esk3_0),esk5_0)
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,esk3_0),esk5_0),k3_orders_2(esk2_0,esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk2_0,esk4_0,esk3_0),esk5_0)
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,esk3_0),esk5_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_12]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | ~ r2_hidden(esk1_3(X2,X1,esk5_0),esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk2_0,esk4_0,esk3_0),esk5_0)
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,esk3_0),esk5_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_14]),c_0_31])]),c_0_19]),c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,X2))
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,k3_orders_2(esk2_0,esk5_0,X2)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,X2))
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,k3_orders_2(esk2_0,esk5_0,X2)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk2_0,esk4_0,esk3_0),esk5_0)
    | ~ m1_subset_1(k3_orders_2(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_12])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk2_0,esk4_0,X1),k3_orders_2(esk2_0,esk5_0,X2))
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,X1),k3_orders_2(esk2_0,esk5_0,X2)),k3_orders_2(esk2_0,esk4_0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk2_0,esk4_0,X1),k3_orders_2(esk2_0,esk5_0,X2))
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,X1),k3_orders_2(esk2_0,esk5_0,X2)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(esk5_0))
    | ~ m1_subset_1(k3_orders_2(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_43])).

cnf(c_0_47,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk2_0,esk4_0,X1),k3_orders_2(esk2_0,esk5_0,esk3_0))
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,X1),k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,esk4_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(k3_orders_2(esk2_0,esk4_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k3_orders_2(esk2_0,esk4_0,X1),k3_orders_2(esk2_0,esk5_0,esk3_0))
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,X1),k3_orders_2(esk2_0,esk5_0,esk3_0)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_25]),c_0_31])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,X2))
    | ~ r2_orders_2(esk2_0,X1,X2)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_12]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_53,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,esk4_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_31]),c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_31]),c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,X2))
    | ~ r2_orders_2(esk2_0,esk1_3(X3,X1,k3_orders_2(esk2_0,esk5_0,X2)),X2)
    | ~ r2_hidden(esk1_3(X3,X1,k3_orders_2(esk2_0,esk5_0,X2)),esk5_0)
    | ~ m1_subset_1(esk1_3(X3,X1,k3_orders_2(esk2_0,esk5_0,X2)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k3_orders_2(esk2_0,esk5_0,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r2_orders_2(esk2_0,esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_14]),c_0_31]),c_0_55])]),c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( ~ m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(k3_orders_2(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_55]),c_0_31])]),c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( ~ m1_subset_1(k3_orders_2(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_38]),c_0_31])])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_25]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:31:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.48  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.48  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.48  #
% 0.19/0.48  # Preprocessing time       : 0.051 s
% 0.19/0.48  # Presaturation interreduction done
% 0.19/0.48  
% 0.19/0.48  # Proof found!
% 0.19/0.48  # SZS status Theorem
% 0.19/0.48  # SZS output start CNFRefutation
% 0.19/0.48  fof(t65_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,X4)=>r1_tarski(k3_orders_2(X1,X3,X2),k3_orders_2(X1,X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_orders_2)).
% 0.19/0.48  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 0.19/0.48  fof(dt_k3_orders_2, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 0.19/0.48  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.48  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.48  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 0.19/0.48  fof(c_0_6, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,X4)=>r1_tarski(k3_orders_2(X1,X3,X2),k3_orders_2(X1,X4,X2)))))))), inference(assume_negation,[status(cth)],[t65_orders_2])).
% 0.19/0.48  fof(c_0_7, plain, ![X8, X9, X10]:((m1_subset_1(esk1_3(X8,X9,X10),X8)|r1_tarski(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8)))&((r2_hidden(esk1_3(X8,X9,X10),X9)|r1_tarski(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8)))&(~r2_hidden(esk1_3(X8,X9,X10),X10)|r1_tarski(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 0.19/0.48  fof(c_0_8, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(r1_tarski(esk4_0,esk5_0)&~r1_tarski(k3_orders_2(esk2_0,esk4_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.19/0.48  fof(c_0_9, plain, ![X14, X15, X16]:(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~m1_subset_1(X16,u1_struct_0(X14))|m1_subset_1(k3_orders_2(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).
% 0.19/0.48  fof(c_0_10, plain, ![X12, X13]:((~m1_subset_1(X12,k1_zfmisc_1(X13))|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|m1_subset_1(X12,k1_zfmisc_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.48  cnf(c_0_11, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.48  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.48  cnf(c_0_13, plain, (v2_struct_0(X1)|m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.48  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.48  cnf(c_0_15, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.48  cnf(c_0_16, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.48  cnf(c_0_17, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.48  cnf(c_0_18, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.48  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.48  cnf(c_0_20, plain, (m1_subset_1(esk1_3(X1,X2,X3),X1)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.48  fof(c_0_21, plain, ![X5, X6, X7]:(~m1_subset_1(X6,k1_zfmisc_1(X5))|(~r2_hidden(X7,X6)|r2_hidden(X7,X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.48  cnf(c_0_22, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.48  cnf(c_0_23, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.48  cnf(c_0_24, negated_conjecture, (r1_tarski(X1,esk5_0)|r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,esk5_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.48  cnf(c_0_25, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.48  cnf(c_0_26, negated_conjecture, (r1_tarski(X1,esk5_0)|m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,esk5_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_20, c_0_12])).
% 0.19/0.48  cnf(c_0_27, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.48  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.48  fof(c_0_29, plain, ![X17, X18, X19, X20]:(((r2_orders_2(X17,X18,X19)|~r2_hidden(X18,k3_orders_2(X17,X20,X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17)))&(r2_hidden(X18,X20)|~r2_hidden(X18,k3_orders_2(X17,X20,X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17))))&(~r2_orders_2(X17,X18,X19)|~r2_hidden(X18,X20)|r2_hidden(X18,k3_orders_2(X17,X20,X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 0.19/0.48  cnf(c_0_30, negated_conjecture, (r1_tarski(k3_orders_2(esk2_0,esk4_0,X1),esk5_0)|r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,X1),esk5_0),k3_orders_2(esk2_0,esk4_0,X1))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.48  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.48  cnf(c_0_32, negated_conjecture, (r1_tarski(k3_orders_2(esk2_0,esk4_0,X1),esk5_0)|m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,X1),esk5_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_26, c_0_25])).
% 0.19/0.48  cnf(c_0_33, plain, (r1_tarski(X2,X3)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.48  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.48  cnf(c_0_35, plain, (r2_hidden(X1,X2)|v2_struct_0(X3)|~r2_hidden(X1,k3_orders_2(X3,X2,X4))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.48  cnf(c_0_36, negated_conjecture, (r1_tarski(k3_orders_2(esk2_0,esk4_0,esk3_0),esk5_0)|r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,esk3_0),esk5_0),k3_orders_2(esk2_0,esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.48  cnf(c_0_37, negated_conjecture, (r1_tarski(k3_orders_2(esk2_0,esk4_0,esk3_0),esk5_0)|m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,esk3_0),esk5_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_31])).
% 0.19/0.48  cnf(c_0_38, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_12]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.48  cnf(c_0_39, negated_conjecture, (r1_tarski(X1,esk5_0)|~r2_hidden(esk1_3(X2,X1,esk5_0),esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.48  cnf(c_0_40, negated_conjecture, (r1_tarski(k3_orders_2(esk2_0,esk4_0,esk3_0),esk5_0)|r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,esk3_0),esk5_0),esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_14]), c_0_31])]), c_0_19]), c_0_37])).
% 0.19/0.48  cnf(c_0_41, negated_conjecture, (r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,X2))|r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,k3_orders_2(esk2_0,esk5_0,X2)),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_11, c_0_38])).
% 0.19/0.48  cnf(c_0_42, negated_conjecture, (r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,X2))|m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,k3_orders_2(esk2_0,esk5_0,X2)),u1_struct_0(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_20, c_0_38])).
% 0.19/0.48  cnf(c_0_43, negated_conjecture, (r1_tarski(k3_orders_2(esk2_0,esk4_0,esk3_0),esk5_0)|~m1_subset_1(k3_orders_2(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_12])])).
% 0.19/0.48  cnf(c_0_44, negated_conjecture, (r1_tarski(k3_orders_2(esk2_0,esk4_0,X1),k3_orders_2(esk2_0,esk5_0,X2))|r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,X1),k3_orders_2(esk2_0,esk5_0,X2)),k3_orders_2(esk2_0,esk4_0,X1))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_41, c_0_25])).
% 0.19/0.48  cnf(c_0_45, negated_conjecture, (r1_tarski(k3_orders_2(esk2_0,esk4_0,X1),k3_orders_2(esk2_0,esk5_0,X2))|m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,X1),k3_orders_2(esk2_0,esk5_0,X2)),u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_42, c_0_25])).
% 0.19/0.48  cnf(c_0_46, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(esk5_0))|~m1_subset_1(k3_orders_2(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_22, c_0_43])).
% 0.19/0.48  cnf(c_0_47, plain, (r2_hidden(X2,k3_orders_2(X1,X4,X3))|v2_struct_0(X1)|~r2_orders_2(X1,X2,X3)|~r2_hidden(X2,X4)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.48  cnf(c_0_48, negated_conjecture, (r1_tarski(k3_orders_2(esk2_0,esk4_0,X1),k3_orders_2(esk2_0,esk5_0,esk3_0))|r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,X1),k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,esk4_0,X1))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_44, c_0_31])).
% 0.19/0.48  cnf(c_0_49, negated_conjecture, (~r1_tarski(k3_orders_2(esk2_0,esk4_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.48  cnf(c_0_50, negated_conjecture, (r1_tarski(k3_orders_2(esk2_0,esk4_0,X1),k3_orders_2(esk2_0,esk5_0,esk3_0))|m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,X1),k3_orders_2(esk2_0,esk5_0,esk3_0)),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_45, c_0_31])).
% 0.19/0.48  cnf(c_0_51, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_25]), c_0_31])])).
% 0.19/0.48  cnf(c_0_52, negated_conjecture, (r2_hidden(X1,k3_orders_2(esk2_0,esk5_0,X2))|~r2_orders_2(esk2_0,X1,X2)|~r2_hidden(X1,esk5_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_12]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.48  cnf(c_0_53, plain, (r2_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(X2,k3_orders_2(X1,X4,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.48  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),k3_orders_2(esk2_0,esk4_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_31]), c_0_49])).
% 0.19/0.48  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_31]), c_0_49])).
% 0.19/0.48  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k3_orders_2(esk2_0,esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_51])).
% 0.19/0.48  cnf(c_0_57, negated_conjecture, (r1_tarski(X1,k3_orders_2(esk2_0,esk5_0,X2))|~r2_orders_2(esk2_0,esk1_3(X3,X1,k3_orders_2(esk2_0,esk5_0,X2)),X2)|~r2_hidden(esk1_3(X3,X1,k3_orders_2(esk2_0,esk5_0,X2)),esk5_0)|~m1_subset_1(esk1_3(X3,X1,k3_orders_2(esk2_0,esk5_0,X2)),u1_struct_0(esk2_0))|~m1_subset_1(k3_orders_2(esk2_0,esk5_0,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_33, c_0_52])).
% 0.19/0.48  cnf(c_0_58, negated_conjecture, (r2_orders_2(esk2_0,esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_14]), c_0_31]), c_0_55])]), c_0_19])).
% 0.19/0.48  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk2_0),k3_orders_2(esk2_0,esk4_0,esk3_0),k3_orders_2(esk2_0,esk5_0,esk3_0)),esk5_0)), inference(spm,[status(thm)],[c_0_56, c_0_54])).
% 0.19/0.48  cnf(c_0_60, negated_conjecture, (~m1_subset_1(k3_orders_2(esk2_0,esk5_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(k3_orders_2(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_55]), c_0_31])]), c_0_49])).
% 0.19/0.48  cnf(c_0_61, negated_conjecture, (~m1_subset_1(k3_orders_2(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_38]), c_0_31])])).
% 0.19/0.48  cnf(c_0_62, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_25]), c_0_31])]), ['proof']).
% 0.19/0.48  # SZS output end CNFRefutation
% 0.19/0.48  # Proof object total steps             : 63
% 0.19/0.48  # Proof object clause steps            : 50
% 0.19/0.48  # Proof object formula steps           : 13
% 0.19/0.48  # Proof object conjectures             : 44
% 0.19/0.48  # Proof object clause conjectures      : 41
% 0.19/0.48  # Proof object formula conjectures     : 3
% 0.19/0.48  # Proof object initial clauses used    : 19
% 0.19/0.48  # Proof object initial formulas used   : 6
% 0.19/0.48  # Proof object generating inferences   : 31
% 0.19/0.48  # Proof object simplifying inferences  : 51
% 0.19/0.48  # Training examples: 0 positive, 0 negative
% 0.19/0.48  # Parsed axioms                        : 6
% 0.19/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.48  # Initial clauses                      : 20
% 0.19/0.48  # Removed in clause preprocessing      : 0
% 0.19/0.48  # Initial clauses in saturation        : 20
% 0.19/0.48  # Processed clauses                    : 306
% 0.19/0.48  # ...of these trivial                  : 3
% 0.19/0.48  # ...subsumed                          : 22
% 0.19/0.48  # ...remaining for further processing  : 281
% 0.19/0.48  # Other redundant clauses eliminated   : 0
% 0.19/0.48  # Clauses deleted for lack of memory   : 0
% 0.19/0.48  # Backward-subsumed                    : 2
% 0.19/0.48  # Backward-rewritten                   : 23
% 0.19/0.48  # Generated clauses                    : 2260
% 0.19/0.48  # ...of the previous two non-trivial   : 2232
% 0.19/0.48  # Contextual simplify-reflections      : 6
% 0.19/0.48  # Paramodulations                      : 2260
% 0.19/0.48  # Factorizations                       : 0
% 0.19/0.48  # Equation resolutions                 : 0
% 0.19/0.48  # Propositional unsat checks           : 0
% 0.19/0.48  #    Propositional check models        : 0
% 0.19/0.48  #    Propositional check unsatisfiable : 0
% 0.19/0.48  #    Propositional clauses             : 0
% 0.19/0.48  #    Propositional clauses after purity: 0
% 0.19/0.48  #    Propositional unsat core size     : 0
% 0.19/0.48  #    Propositional preprocessing time  : 0.000
% 0.19/0.48  #    Propositional encoding time       : 0.000
% 0.19/0.48  #    Propositional solver time         : 0.000
% 0.19/0.48  #    Success case prop preproc time    : 0.000
% 0.19/0.48  #    Success case prop encoding time   : 0.000
% 0.19/0.48  #    Success case prop solver time     : 0.000
% 0.19/0.48  # Current number of processed clauses  : 236
% 0.19/0.48  #    Positive orientable unit clauses  : 32
% 0.19/0.48  #    Positive unorientable unit clauses: 0
% 0.19/0.48  #    Negative unit clauses             : 5
% 0.19/0.48  #    Non-unit-clauses                  : 199
% 0.19/0.48  # Current number of unprocessed clauses: 1951
% 0.19/0.48  # ...number of literals in the above   : 7597
% 0.19/0.48  # Current number of archived formulas  : 0
% 0.19/0.48  # Current number of archived clauses   : 45
% 0.19/0.48  # Clause-clause subsumption calls (NU) : 10682
% 0.19/0.48  # Rec. Clause-clause subsumption calls : 5273
% 0.19/0.48  # Non-unit clause-clause subsumptions  : 29
% 0.19/0.48  # Unit Clause-clause subsumption calls : 772
% 0.19/0.48  # Rewrite failures with RHS unbound    : 0
% 0.19/0.48  # BW rewrite match attempts            : 52
% 0.19/0.48  # BW rewrite match successes           : 8
% 0.19/0.48  # Condensation attempts                : 0
% 0.19/0.48  # Condensation successes               : 0
% 0.19/0.48  # Termbank termtop insertions          : 107478
% 0.19/0.48  
% 0.19/0.48  # -------------------------------------------------
% 0.19/0.48  # User time                : 0.129 s
% 0.19/0.48  # System time              : 0.011 s
% 0.19/0.48  # Total time               : 0.140 s
% 0.19/0.48  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
