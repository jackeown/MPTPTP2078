%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:30 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 299 expanded)
%              Number of clauses        :   38 ( 120 expanded)
%              Number of leaves         :   10 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  233 (1767 expanded)
%              Number of equality atoms :   21 (  97 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   2 average)
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

fof(dt_k3_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X28,X29] :
      ( ( ~ v1_subset_1(X29,X28)
        | X29 != X28
        | ~ m1_subset_1(X29,k1_zfmisc_1(X28)) )
      & ( X29 = X28
        | v1_subset_1(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_12,plain,(
    ! [X12] :
      ( m1_subset_1(esk2_1(X12),k1_zfmisc_1(X12))
      & ~ v1_subset_1(esk2_1(X12),X12) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).

fof(c_0_13,plain,(
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

fof(c_0_14,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

cnf(c_0_15,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( ~ v1_subset_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ v13_waybel_0(X23,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r2_hidden(X24,X23)
        | ~ r1_orders_2(X22,X24,X25)
        | r2_hidden(X25,X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk3_2(X22,X23),u1_struct_0(X22))
        | v13_waybel_0(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk4_2(X22,X23),u1_struct_0(X22))
        | v13_waybel_0(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_orders_2(X22) )
      & ( r2_hidden(esk3_2(X22,X23),X23)
        | v13_waybel_0(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_orders_2(X22) )
      & ( r1_orders_2(X22,esk3_2(X22,X23),esk4_2(X22,X23))
        | v13_waybel_0(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_orders_2(X22) )
      & ( ~ r2_hidden(esk4_2(X22,X23),X23)
        | v13_waybel_0(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_19,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | m1_subset_1(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X1)
    | X2 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( esk2_1(X1) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

fof(c_0_23,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ r2_hidden(X7,X6)
      | r2_hidden(X7,X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( X1 = esk6_0
    | m1_subset_1(esk1_3(u1_struct_0(esk5_0),X1,esk6_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_22])).

cnf(c_0_28,plain,
    ( X2 = X3
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | m1_subset_1(esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( X1 = esk6_0
    | ~ r2_hidden(esk1_3(u1_struct_0(esk5_0),X1,esk6_0),esk6_0)
    | ~ r2_hidden(esk1_3(u1_struct_0(esk5_0),X1,esk6_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_21])).

fof(c_0_35,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ v5_orders_2(X20)
      | ~ v1_yellow_0(X20)
      | ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | r1_orders_2(X20,k3_yellow_0(X20),X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).

cnf(c_0_36,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r2_hidden(esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0),X1)
    | ~ v13_waybel_0(X1,esk5_0)
    | ~ r1_orders_2(esk5_0,X2,esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_37,negated_conjecture,
    ( v13_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | ~ r2_hidden(esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_27]),c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk5_0),esk6_0)
    | ~ v1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | v1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_21])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,k3_yellow_0(X1),X2)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( v1_yellow_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_45,plain,(
    ! [X19] :
      ( ~ l1_orders_2(X19)
      | m1_subset_1(k3_yellow_0(X19),u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).

cnf(c_0_46,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | ~ r1_orders_2(esk5_0,X1,esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_21])]),c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r2_hidden(k3_yellow_0(esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0
    | r1_orders_2(esk5_0,k3_yellow_0(esk5_0),esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_31]),c_0_42]),c_0_43]),c_0_32])]),c_0_44])).

fof(c_0_49,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,X15)
      | v1_xboole_0(X15)
      | r2_hidden(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_50,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( u1_struct_0(esk5_0) = esk6_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( v1_subset_1(esk6_0,u1_struct_0(esk5_0))
    | ~ r2_hidden(k3_yellow_0(esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k3_yellow_0(esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_32])])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(k3_yellow_0(esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_51]),c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:02:55 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  # Version: 2.5pre002
% 0.21/0.36  # No SInE strategy applied
% 0.21/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.21/0.39  # and selection function SelectNewComplexAHPNS.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.031 s
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.21/0.39  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.21/0.39  fof(rc3_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_subset_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 0.21/0.39  fof(t8_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 0.21/0.39  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.21/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.21/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.21/0.39  fof(t44_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,k3_yellow_0(X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 0.21/0.39  fof(dt_k3_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 0.21/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.21/0.39  fof(c_0_10, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.21/0.39  fof(c_0_11, plain, ![X28, X29]:((~v1_subset_1(X29,X28)|X29!=X28|~m1_subset_1(X29,k1_zfmisc_1(X28)))&(X29=X28|v1_subset_1(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.21/0.39  fof(c_0_12, plain, ![X12]:(m1_subset_1(esk2_1(X12),k1_zfmisc_1(X12))&~v1_subset_1(esk2_1(X12),X12)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).
% 0.21/0.39  fof(c_0_13, plain, ![X8, X9, X10]:((m1_subset_1(esk1_3(X8,X9,X10),X8)|X9=X10|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8)))&((~r2_hidden(esk1_3(X8,X9,X10),X9)|~r2_hidden(esk1_3(X8,X9,X10),X10)|X9=X10|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8)))&(r2_hidden(esk1_3(X8,X9,X10),X9)|r2_hidden(esk1_3(X8,X9,X10),X10)|X9=X10|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_subset_1])])])])])).
% 0.21/0.39  fof(c_0_14, negated_conjecture, ((((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&v1_yellow_0(esk5_0))&l1_orders_2(esk5_0))&((((~v1_xboole_0(esk6_0)&v2_waybel_0(esk6_0,esk5_0))&v13_waybel_0(esk6_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))))&((~v1_subset_1(esk6_0,u1_struct_0(esk5_0))|r2_hidden(k3_yellow_0(esk5_0),esk6_0))&(v1_subset_1(esk6_0,u1_struct_0(esk5_0))|~r2_hidden(k3_yellow_0(esk5_0),esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.21/0.39  cnf(c_0_15, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_16, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_17, plain, (~v1_subset_1(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  fof(c_0_18, plain, ![X22, X23, X24, X25]:((~v13_waybel_0(X23,X22)|(~m1_subset_1(X24,u1_struct_0(X22))|(~m1_subset_1(X25,u1_struct_0(X22))|(~r2_hidden(X24,X23)|~r1_orders_2(X22,X24,X25)|r2_hidden(X25,X23))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_orders_2(X22))&((m1_subset_1(esk3_2(X22,X23),u1_struct_0(X22))|v13_waybel_0(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_orders_2(X22))&((m1_subset_1(esk4_2(X22,X23),u1_struct_0(X22))|v13_waybel_0(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_orders_2(X22))&(((r2_hidden(esk3_2(X22,X23),X23)|v13_waybel_0(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_orders_2(X22))&(r1_orders_2(X22,esk3_2(X22,X23),esk4_2(X22,X23))|v13_waybel_0(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_orders_2(X22)))&(~r2_hidden(esk4_2(X22,X23),X23)|v13_waybel_0(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_orders_2(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.21/0.39  fof(c_0_19, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|m1_subset_1(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.21/0.39  cnf(c_0_20, plain, (m1_subset_1(esk1_3(X1,X2,X3),X1)|X2=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_22, plain, (esk2_1(X1)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.21/0.39  fof(c_0_23, plain, ![X5, X6, X7]:(~m1_subset_1(X6,k1_zfmisc_1(X5))|(~r2_hidden(X7,X6)|r2_hidden(X7,X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.21/0.39  cnf(c_0_24, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.39  cnf(c_0_25, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.39  cnf(c_0_26, negated_conjecture, (X1=esk6_0|m1_subset_1(esk1_3(u1_struct_0(esk5_0),X1,esk6_0),u1_struct_0(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.39  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_16, c_0_22])).
% 0.21/0.39  cnf(c_0_28, plain, (X2=X3|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_29, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.39  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~r2_hidden(X4,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))), inference(csr,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.39  cnf(c_0_31, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|m1_subset_1(esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.39  cnf(c_0_32, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_33, negated_conjecture, (X1=esk6_0|~r2_hidden(esk1_3(u1_struct_0(esk5_0),X1,esk6_0),esk6_0)|~r2_hidden(esk1_3(u1_struct_0(esk5_0),X1,esk6_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_28, c_0_21])).
% 0.21/0.39  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_29, c_0_21])).
% 0.21/0.39  fof(c_0_35, plain, ![X20, X21]:(v2_struct_0(X20)|~v5_orders_2(X20)|~v1_yellow_0(X20)|~l1_orders_2(X20)|(~m1_subset_1(X21,u1_struct_0(X20))|r1_orders_2(X20,k3_yellow_0(X20),X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_yellow_0])])])])).
% 0.21/0.39  cnf(c_0_36, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r2_hidden(esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0),X1)|~v13_waybel_0(X1,esk5_0)|~r1_orders_2(esk5_0,X2,esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0))|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.21/0.39  cnf(c_0_37, negated_conjecture, (v13_waybel_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_38, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|~r2_hidden(esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_27]), c_0_34])).
% 0.21/0.39  cnf(c_0_39, negated_conjecture, (r2_hidden(k3_yellow_0(esk5_0),esk6_0)|~v1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|v1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_15, c_0_21])).
% 0.21/0.39  cnf(c_0_41, plain, (v2_struct_0(X1)|r1_orders_2(X1,k3_yellow_0(X1),X2)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.39  cnf(c_0_42, negated_conjecture, (v1_yellow_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_43, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  fof(c_0_45, plain, ![X19]:(~l1_orders_2(X19)|m1_subset_1(k3_yellow_0(X19),u1_struct_0(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).
% 0.21/0.39  cnf(c_0_46, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|~r1_orders_2(esk5_0,X1,esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0))|~r2_hidden(X1,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_21])]), c_0_38])).
% 0.21/0.39  cnf(c_0_47, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r2_hidden(k3_yellow_0(esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.39  cnf(c_0_48, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0|r1_orders_2(esk5_0,k3_yellow_0(esk5_0),esk1_3(u1_struct_0(esk5_0),u1_struct_0(esk5_0),esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_31]), c_0_42]), c_0_43]), c_0_32])]), c_0_44])).
% 0.21/0.39  fof(c_0_49, plain, ![X14, X15]:(~m1_subset_1(X14,X15)|(v1_xboole_0(X15)|r2_hidden(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.21/0.39  cnf(c_0_50, plain, (m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.39  cnf(c_0_51, negated_conjecture, (u1_struct_0(esk5_0)=esk6_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.21/0.39  cnf(c_0_52, negated_conjecture, (v1_subset_1(esk6_0,u1_struct_0(esk5_0))|~r2_hidden(k3_yellow_0(esk5_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_53, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_17, c_0_22])).
% 0.21/0.39  cnf(c_0_54, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.39  cnf(c_0_55, negated_conjecture, (m1_subset_1(k3_yellow_0(esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_32])])).
% 0.21/0.39  cnf(c_0_56, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_57, negated_conjecture, (~r2_hidden(k3_yellow_0(esk5_0),esk6_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_51]), c_0_53])).
% 0.21/0.39  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 59
% 0.21/0.39  # Proof object clause steps            : 38
% 0.21/0.39  # Proof object formula steps           : 21
% 0.21/0.39  # Proof object conjectures             : 26
% 0.21/0.39  # Proof object clause conjectures      : 23
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 20
% 0.21/0.39  # Proof object initial formulas used   : 10
% 0.21/0.39  # Proof object generating inferences   : 14
% 0.21/0.39  # Proof object simplifying inferences  : 22
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 10
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 30
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 30
% 0.21/0.39  # Processed clauses                    : 71
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 8
% 0.21/0.39  # ...remaining for further processing  : 63
% 0.21/0.39  # Other redundant clauses eliminated   : 1
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 2
% 0.21/0.39  # Backward-rewritten                   : 25
% 0.21/0.39  # Generated clauses                    : 70
% 0.21/0.39  # ...of the previous two non-trivial   : 71
% 0.21/0.39  # Contextual simplify-reflections      : 5
% 0.21/0.39  # Paramodulations                      : 69
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 1
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 35
% 0.21/0.39  #    Positive orientable unit clauses  : 11
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 4
% 0.21/0.39  #    Non-unit-clauses                  : 20
% 0.21/0.39  # Current number of unprocessed clauses: 21
% 0.21/0.39  # ...number of literals in the above   : 65
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 27
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 325
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 124
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 14
% 0.21/0.39  # Unit Clause-clause subsumption calls : 6
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 10
% 0.21/0.39  # BW rewrite match successes           : 3
% 0.21/0.39  # Condensation attempts                : 71
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 3658
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.033 s
% 0.21/0.39  # System time              : 0.006 s
% 0.21/0.39  # Total time               : 0.039 s
% 0.21/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
