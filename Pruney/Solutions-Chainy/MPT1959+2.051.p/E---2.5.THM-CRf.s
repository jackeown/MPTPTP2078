%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:30 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 885 expanded)
%              Number of clauses        :   45 ( 354 expanded)
%              Number of leaves         :   11 ( 221 expanded)
%              Depth                    :   12
%              Number of atoms          :  278 (5375 expanded)
%              Number of equality atoms :   21 ( 281 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_waybel_7,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v1_subset_1(X2,u1_struct_0(X1))
          <=> ~ r2_hidden(k3_yellow_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(rc3_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & ~ v1_subset_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

fof(t8_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                <=> r2_hidden(X4,X3) ) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(d20_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v13_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r1_orders_2(X1,X3,X4) )
                     => r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t44_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,k3_yellow_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

fof(t17_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k5_waybel_0(X1,X2))
              <=> r1_orders_2(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_waybel_0)).

fof(dt_k3_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(dt_k5_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_yellow_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v2_waybel_0(X2,X1)
              & v13_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v1_subset_1(X2,u1_struct_0(X1))
            <=> ~ r2_hidden(k3_yellow_0(X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_waybel_7])).

fof(c_0_12,plain,(
    ! [X31,X32] :
      ( ( ~ v1_subset_1(X32,X31)
        | X32 != X31
        | ~ m1_subset_1(X32,k1_zfmisc_1(X31)) )
      & ( X32 = X31
        | v1_subset_1(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_13,plain,(
    ! [X12] :
      ( m1_subset_1(esk2_1(X12),k1_zfmisc_1(X12))
      & ~ v1_subset_1(esk2_1(X12),X12) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).

fof(c_0_14,plain,(
    ! [X8,X9,X10] :
      ( ( m1_subset_1(esk1_3(X8,X9,X10),X8)
        | X9 = X10
        | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) )
      & ( ~ r2_hidden(esk1_3(X8,X9,X10),X9)
        | ~ r2_hidden(esk1_3(X8,X9,X10),X10)
        | X9 = X10
        | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) )
      & ( r2_hidden(esk1_3(X8,X9,X10),X9)
        | r2_hidden(esk1_3(X8,X9,X10),X10)
        | X9 = X10
        | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & v1_yellow_0(esk5_0)
    & l1_orders_2(esk5_0)
    & ~ v1_xboole_0(esk6_0)
    & v2_waybel_0(esk6_0,esk5_0)
    & v13_waybel_0(esk6_0,esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ( ~ v1_subset_1(esk6_0,u1_struct_0(esk5_0))
      | r2_hidden(k3_yellow_0(esk5_0),esk6_0) )
    & ( v1_subset_1(esk6_0,u1_struct_0(esk5_0))
      | ~ r2_hidden(k3_yellow_0(esk5_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

cnf(c_0_16,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( ~ v1_subset_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X20,X21,X22,X23] :
      ( ( ~ v13_waybel_0(X21,X20)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ r2_hidden(X22,X21)
        | ~ r1_orders_2(X20,X22,X23)
        | r2_hidden(X23,X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_orders_2(X20) )
      & ( m1_subset_1(esk3_2(X20,X21),u1_struct_0(X20))
        | v13_waybel_0(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_orders_2(X20) )
      & ( m1_subset_1(esk4_2(X20,X21),u1_struct_0(X20))
        | v13_waybel_0(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_orders_2(X20) )
      & ( r2_hidden(esk3_2(X20,X21),X21)
        | v13_waybel_0(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_orders_2(X20) )
      & ( r1_orders_2(X20,esk3_2(X20,X21),esk4_2(X20,X21))
        | v13_waybel_0(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_orders_2(X20) )
      & ( ~ r2_hidden(esk4_2(X20,X21),X21)
        | v13_waybel_0(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_orders_2(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_20,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(X14,X15)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X16))
      | m1_subset_1(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X1)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( esk2_1(X1) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

fof(c_0_24,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ r2_hidden(X7,X6)
      | r2_hidden(X7,X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_25,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( X1 = esk6_0
    | m1_subset_1(esk1_3(u1_struct_0(esk5_0),X1,esk6_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_23])).

cnf(c_0_29,plain,
    ( X2 = X3
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | m1_subset_1(esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( X1 = esk6_0
    | ~ r2_hidden(esk1_3(u1_struct_0(esk5_0),X1,esk6_0),esk6_0)
    | ~ r2_hidden(esk1_3(u1_struct_0(esk5_0),X1,esk6_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_22])).

fof(c_0_36,plain,(
    ! [X18,X19] :
      ( v2_struct_0(X18)
      | ~ v5_orders_2(X18)
      | ~ v1_yellow_0(X18)
      | ~ l1_orders_2(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | r1_orders_2(X18,k3_yellow_0(X18),X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).

cnf(c_0_37,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r2_hidden(esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0),X1)
    | ~ v13_waybel_0(X1,esk5_0)
    | ~ r1_orders_2(esk5_0,X2,esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_38,negated_conjecture,
    ( v13_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | ~ r2_hidden(esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_28]),c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk5_0),esk6_0)
    | ~ v1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | v1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_22])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),X2)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( v1_yellow_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_46,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r2_hidden(X30,k5_waybel_0(X28,X29))
        | r1_orders_2(X28,X30,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ l1_orders_2(X28) )
      & ( ~ r1_orders_2(X28,X30,X29)
        | r2_hidden(X30,k5_waybel_0(X28,X29))
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_waybel_0])])])])])).

fof(c_0_47,plain,(
    ! [X17] :
      ( ~ l1_orders_2(X17)
      | m1_subset_1(k3_yellow_0(X17),u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).

cnf(c_0_48,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | ~ r1_orders_2(esk5_0,X1,esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_22])]),c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r2_hidden(k3_yellow_0(esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r1_orders_2(esk5_0,k3_yellow_0(esk5_0),esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_32]),c_0_43]),c_0_44]),c_0_33])]),c_0_45])).

fof(c_0_51,plain,(
    ! [X26,X27] :
      ( v2_struct_0(X26)
      | ~ l1_orders_2(X26)
      | ~ m1_subset_1(X27,u1_struct_0(X26))
      | m1_subset_1(k5_waybel_0(X26,X27),k1_zfmisc_1(u1_struct_0(X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_0])])])).

cnf(c_0_52,plain,
    ( r2_hidden(X2,k5_waybel_0(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k5_waybel_0(X1,k3_yellow_0(X1)))
    | ~ r1_orders_2(X1,X2,k3_yellow_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk5_0,k3_yellow_0(esk5_0),X1)
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_54]),c_0_43]),c_0_44]),c_0_33])]),c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k3_yellow_0(esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_33])])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_waybel_0(X1,k3_yellow_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,k5_waybel_0(esk5_0,k3_yellow_0(esk5_0)))
    | ~ r1_orders_2(esk5_0,X1,k3_yellow_0(esk5_0))
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_54]),c_0_33])]),c_0_45])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk5_0,k3_yellow_0(esk5_0),k3_yellow_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( v1_subset_1(esk6_0,u1_struct_0(esk5_0))
    | ~ r2_hidden(k3_yellow_0(esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_63,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_18,c_0_23])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(X2,k5_waybel_0(X1,k3_yellow_0(X1))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk5_0),k5_waybel_0(esk5_0,k3_yellow_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_58]),c_0_61])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(k3_yellow_0(esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_54]),c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_54]),c_0_33])]),c_0_45]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:56:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.20/0.40  # and selection function SelectNewComplexAHPNS.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.029 s
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.20/0.40  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.20/0.40  fof(rc3_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_subset_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 0.20/0.40  fof(t8_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 0.20/0.40  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.20/0.40  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.40  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.20/0.40  fof(t44_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,k3_yellow_0(X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 0.20/0.40  fof(t17_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k5_waybel_0(X1,X2))<=>r1_orders_2(X1,X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_waybel_0)).
% 0.20/0.40  fof(dt_k3_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 0.20/0.40  fof(dt_k5_waybel_0, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_waybel_0)).
% 0.20/0.40  fof(c_0_11, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.20/0.40  fof(c_0_12, plain, ![X31, X32]:((~v1_subset_1(X32,X31)|X32!=X31|~m1_subset_1(X32,k1_zfmisc_1(X31)))&(X32=X31|v1_subset_1(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.20/0.40  fof(c_0_13, plain, ![X12]:(m1_subset_1(esk2_1(X12),k1_zfmisc_1(X12))&~v1_subset_1(esk2_1(X12),X12)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).
% 0.20/0.40  fof(c_0_14, plain, ![X8, X9, X10]:((m1_subset_1(esk1_3(X8,X9,X10),X8)|X9=X10|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8)))&((~r2_hidden(esk1_3(X8,X9,X10),X9)|~r2_hidden(esk1_3(X8,X9,X10),X10)|X9=X10|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8)))&(r2_hidden(esk1_3(X8,X9,X10),X9)|r2_hidden(esk1_3(X8,X9,X10),X10)|X9=X10|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).
% 0.20/0.40  fof(c_0_15, negated_conjecture, ((((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&v1_yellow_0(esk5_0))&l1_orders_2(esk5_0))&((((~v1_xboole_0(esk6_0)&v2_waybel_0(esk6_0,esk5_0))&v13_waybel_0(esk6_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))))&((~v1_subset_1(esk6_0,u1_struct_0(esk5_0))|r2_hidden(k3_yellow_0(esk5_0),esk6_0))&(v1_subset_1(esk6_0,u1_struct_0(esk5_0))|~r2_hidden(k3_yellow_0(esk5_0),esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.20/0.40  cnf(c_0_16, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_17, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_18, plain, (~v1_subset_1(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  fof(c_0_19, plain, ![X20, X21, X22, X23]:((~v13_waybel_0(X21,X20)|(~m1_subset_1(X22,u1_struct_0(X20))|(~m1_subset_1(X23,u1_struct_0(X20))|(~r2_hidden(X22,X21)|~r1_orders_2(X20,X22,X23)|r2_hidden(X23,X21))))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_orders_2(X20))&((m1_subset_1(esk3_2(X20,X21),u1_struct_0(X20))|v13_waybel_0(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_orders_2(X20))&((m1_subset_1(esk4_2(X20,X21),u1_struct_0(X20))|v13_waybel_0(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_orders_2(X20))&(((r2_hidden(esk3_2(X20,X21),X21)|v13_waybel_0(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_orders_2(X20))&(r1_orders_2(X20,esk3_2(X20,X21),esk4_2(X20,X21))|v13_waybel_0(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_orders_2(X20)))&(~r2_hidden(esk4_2(X20,X21),X21)|v13_waybel_0(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_orders_2(X20)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.20/0.40  fof(c_0_20, plain, ![X14, X15, X16]:(~r2_hidden(X14,X15)|~m1_subset_1(X15,k1_zfmisc_1(X16))|m1_subset_1(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.40  cnf(c_0_21, plain, (m1_subset_1(esk1_3(X1,X2,X3),X1)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_23, plain, (esk2_1(X1)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.20/0.40  fof(c_0_24, plain, ![X5, X6, X7]:(~m1_subset_1(X6,k1_zfmisc_1(X5))|(~r2_hidden(X7,X6)|r2_hidden(X7,X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.20/0.40  cnf(c_0_25, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_26, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_27, negated_conjecture, (X1=esk6_0|m1_subset_1(esk1_3(u1_struct_0(esk5_0),X1,esk6_0),u1_struct_0(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.40  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_17, c_0_23])).
% 0.20/0.40  cnf(c_0_29, plain, (X2=X3|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_31, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~r2_hidden(X4,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))), inference(csr,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.40  cnf(c_0_32, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|m1_subset_1(esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (X1=esk6_0|~r2_hidden(esk1_3(u1_struct_0(esk5_0),X1,esk6_0),esk6_0)|~r2_hidden(esk1_3(u1_struct_0(esk5_0),X1,esk6_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_29, c_0_22])).
% 0.20/0.40  cnf(c_0_35, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_22])).
% 0.20/0.40  fof(c_0_36, plain, ![X18, X19]:(v2_struct_0(X18)|~v5_orders_2(X18)|~v1_yellow_0(X18)|~l1_orders_2(X18)|(~m1_subset_1(X19,u1_struct_0(X18))|r1_orders_2(X18,k3_yellow_0(X18),X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).
% 0.20/0.40  cnf(c_0_37, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r2_hidden(esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0),X1)|~v13_waybel_0(X1,esk5_0)|~r1_orders_2(esk5_0,X2,esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0))|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.20/0.40  cnf(c_0_38, negated_conjecture, (v13_waybel_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_39, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|~r2_hidden(esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_28]), c_0_35])).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, (r2_hidden(k3_yellow_0(esk5_0),esk6_0)|~v1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|v1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_16, c_0_22])).
% 0.20/0.40  cnf(c_0_42, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),X2)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (v1_yellow_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  fof(c_0_46, plain, ![X28, X29, X30]:((~r2_hidden(X30,k5_waybel_0(X28,X29))|r1_orders_2(X28,X30,X29)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~l1_orders_2(X28)))&(~r1_orders_2(X28,X30,X29)|r2_hidden(X30,k5_waybel_0(X28,X29))|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~l1_orders_2(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_waybel_0])])])])])).
% 0.20/0.40  fof(c_0_47, plain, ![X17]:(~l1_orders_2(X17)|m1_subset_1(k3_yellow_0(X17),u1_struct_0(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|~r1_orders_2(esk5_0,X1,esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0))|~r2_hidden(X1,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_22])]), c_0_39])).
% 0.20/0.40  cnf(c_0_49, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r2_hidden(k3_yellow_0(esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.40  cnf(c_0_50, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r1_orders_2(esk5_0,k3_yellow_0(esk5_0),esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_32]), c_0_43]), c_0_44]), c_0_33])]), c_0_45])).
% 0.20/0.40  fof(c_0_51, plain, ![X26, X27]:(v2_struct_0(X26)|~l1_orders_2(X26)|~m1_subset_1(X27,u1_struct_0(X26))|m1_subset_1(k5_waybel_0(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_0])])])).
% 0.20/0.40  cnf(c_0_52, plain, (r2_hidden(X2,k5_waybel_0(X1,X3))|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.40  cnf(c_0_53, plain, (m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.40  cnf(c_0_54, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.20/0.40  cnf(c_0_55, plain, (v2_struct_0(X1)|m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.40  cnf(c_0_56, plain, (v2_struct_0(X1)|r2_hidden(X2,k5_waybel_0(X1,k3_yellow_0(X1)))|~r1_orders_2(X1,X2,k3_yellow_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.40  cnf(c_0_57, negated_conjecture, (r1_orders_2(esk5_0,k3_yellow_0(esk5_0),X1)|~m1_subset_1(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_54]), c_0_43]), c_0_44]), c_0_33])]), c_0_45])).
% 0.20/0.40  cnf(c_0_58, negated_conjecture, (m1_subset_1(k3_yellow_0(esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_33])])).
% 0.20/0.40  cnf(c_0_59, plain, (v2_struct_0(X1)|m1_subset_1(k5_waybel_0(X1,k3_yellow_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_55, c_0_53])).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,k5_waybel_0(esk5_0,k3_yellow_0(esk5_0)))|~r1_orders_2(esk5_0,X1,k3_yellow_0(esk5_0))|~m1_subset_1(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_54]), c_0_33])]), c_0_45])).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, (r1_orders_2(esk5_0,k3_yellow_0(esk5_0),k3_yellow_0(esk5_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.40  cnf(c_0_62, negated_conjecture, (v1_subset_1(esk6_0,u1_struct_0(esk5_0))|~r2_hidden(k3_yellow_0(esk5_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_63, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_18, c_0_23])).
% 0.20/0.40  cnf(c_0_64, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~r2_hidden(X2,k5_waybel_0(X1,k3_yellow_0(X1)))), inference(spm,[status(thm)],[c_0_30, c_0_59])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (r2_hidden(k3_yellow_0(esk5_0),k5_waybel_0(esk5_0,k3_yellow_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_58]), c_0_61])])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (~r2_hidden(k3_yellow_0(esk5_0),esk6_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_54]), c_0_63])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_54]), c_0_33])]), c_0_45]), c_0_66]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 68
% 0.20/0.40  # Proof object clause steps            : 45
% 0.20/0.40  # Proof object formula steps           : 23
% 0.20/0.40  # Proof object conjectures             : 29
% 0.20/0.40  # Proof object clause conjectures      : 26
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 20
% 0.20/0.40  # Proof object initial formulas used   : 11
% 0.20/0.40  # Proof object generating inferences   : 21
% 0.20/0.40  # Proof object simplifying inferences  : 35
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 11
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 32
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 32
% 0.20/0.40  # Processed clauses                    : 162
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 28
% 0.20/0.40  # ...remaining for further processing  : 134
% 0.20/0.40  # Other redundant clauses eliminated   : 1
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 79
% 0.20/0.40  # Generated clauses                    : 300
% 0.20/0.40  # ...of the previous two non-trivial   : 299
% 0.20/0.40  # Contextual simplify-reflections      : 11
% 0.20/0.40  # Paramodulations                      : 299
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 1
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 54
% 0.20/0.40  #    Positive orientable unit clauses  : 14
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 4
% 0.20/0.40  #    Non-unit-clauses                  : 36
% 0.20/0.40  # Current number of unprocessed clauses: 159
% 0.20/0.40  # ...number of literals in the above   : 667
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 79
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 1341
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 448
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 37
% 0.20/0.40  # Unit Clause-clause subsumption calls : 56
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 14
% 0.20/0.40  # BW rewrite match successes           : 3
% 0.20/0.40  # Condensation attempts                : 163
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 12553
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.041 s
% 0.20/0.40  # System time              : 0.006 s
% 0.20/0.40  # Total time               : 0.047 s
% 0.20/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
