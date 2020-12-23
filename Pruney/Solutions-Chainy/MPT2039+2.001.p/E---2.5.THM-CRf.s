%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:47 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :  489 (127848826392 expanded)
%              Number of clauses        :  466 (40888859967 expanded)
%              Number of leaves         :   11 (31245345905 expanded)
%              Depth                    :  158
%              Number of atoms          : 2501 (1521014177922 expanded)
%              Number of equality atoms :  259 (4194047584 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal clause size      :   65 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_waybel_9,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & v1_compts_1(X1)
        & l1_waybel_9(X1) )
     => ( ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => v5_pre_topc(k4_waybel_1(X1,X2),X1,X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => ( v10_waybel_0(X2,X1)
             => ( r1_waybel_9(X1,X2)
                & r2_hidden(k1_waybel_2(X1,X2),k10_yellow_6(X1,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_9)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(dt_l1_waybel_9,axiom,(
    ! [X1] :
      ( l1_waybel_9(X1)
     => ( l1_pre_topc(X1)
        & l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(t30_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & v1_compts_1(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r3_waybel_9(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_waybel_9)).

fof(t35_waybel_9,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & v1_compts_1(X1)
        & l1_waybel_9(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v4_orders_2(X3)
                & v7_waybel_0(X3)
                & l1_waybel_0(X3,X1) )
             => ( ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => v5_pre_topc(k4_waybel_1(X1,X4),X1,X1) )
                  & v10_waybel_0(X3,X1)
                  & r3_waybel_9(X1,X3,X2) )
               => X2 = k1_waybel_2(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_waybel_9)).

fof(l48_waybel_9,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & v1_compts_1(X1)
        & l1_waybel_9(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( X3 = X4
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => v5_pre_topc(k4_waybel_1(X1,X5),X1,X1) )
                      & v10_waybel_0(X2,X1)
                      & r3_waybel_9(X1,X2,X3) )
                   => r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l48_waybel_9)).

fof(t15_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r2_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_0)).

fof(t33_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & v1_compts_1(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r3_waybel_9(X1,X2,X3)
                        & r3_waybel_9(X1,X2,X4) )
                     => X3 = X4 ) ) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r3_waybel_9(X1,X2,X3)
                 => r2_hidden(X3,k10_yellow_6(X1,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_waybel_9)).

fof(d3_waybel_9,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ( r1_waybel_9(X1,X2)
          <=> r1_yellow_0(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_waybel_9)).

fof(l49_waybel_9,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & v1_compts_1(X1)
        & l1_waybel_9(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( X3 = X4
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => v5_pre_topc(k4_waybel_1(X1,X5),X1,X1) )
                      & r3_waybel_9(X1,X2,X3) )
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ( r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)
                         => r3_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_waybel_9)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & v8_pre_topc(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & v1_compts_1(X1)
          & l1_waybel_9(X1) )
       => ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => v5_pre_topc(k4_waybel_1(X1,X2),X1,X1) )
         => ! [X2] :
              ( ( ~ v2_struct_0(X2)
                & v4_orders_2(X2)
                & v7_waybel_0(X2)
                & l1_waybel_0(X2,X1) )
             => ( v10_waybel_0(X2,X1)
               => ( r1_waybel_9(X1,X2)
                  & r2_hidden(k1_waybel_2(X1,X2),k10_yellow_6(X1,X2)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_waybel_9])).

fof(c_0_12,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | ~ v1_lattice3(X9)
      | ~ v2_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

fof(c_0_13,negated_conjecture,(
    ! [X44] :
      ( v2_pre_topc(esk9_0)
      & v8_pre_topc(esk9_0)
      & v3_orders_2(esk9_0)
      & v4_orders_2(esk9_0)
      & v5_orders_2(esk9_0)
      & v1_lattice3(esk9_0)
      & v2_lattice3(esk9_0)
      & v1_compts_1(esk9_0)
      & l1_waybel_9(esk9_0)
      & ( ~ m1_subset_1(X44,u1_struct_0(esk9_0))
        | v5_pre_topc(k4_waybel_1(esk9_0,X44),esk9_0,esk9_0) )
      & ~ v2_struct_0(esk10_0)
      & v4_orders_2(esk10_0)
      & v7_waybel_0(esk10_0)
      & l1_waybel_0(esk10_0,esk9_0)
      & v10_waybel_0(esk10_0,esk9_0)
      & ( ~ r1_waybel_9(esk9_0,esk10_0)
        | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).

fof(c_0_14,plain,(
    ! [X19] :
      ( ( l1_pre_topc(X19)
        | ~ l1_waybel_9(X19) )
      & ( l1_orders_2(X19)
        | ~ l1_waybel_9(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).

cnf(c_0_15,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v1_lattice3(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( l1_orders_2(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_waybel_9(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X31,X32] :
      ( ( m1_subset_1(esk5_2(X31,X32),u1_struct_0(X31))
        | v2_struct_0(X32)
        | ~ v4_orders_2(X32)
        | ~ v7_waybel_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ v8_pre_topc(X31)
        | ~ v1_compts_1(X31)
        | ~ l1_pre_topc(X31) )
      & ( r3_waybel_9(X31,X32,esk5_2(X31,X32))
        | v2_struct_0(X32)
        | ~ v4_orders_2(X32)
        | ~ v7_waybel_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ v8_pre_topc(X31)
        | ~ v1_compts_1(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_waybel_9])])])])])])).

cnf(c_0_20,negated_conjecture,
    ( ~ l1_orders_2(esk9_0)
    | ~ v2_struct_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk9_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( l1_waybel_0(esk10_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( v7_waybel_0(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( v1_compts_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( v4_orders_2(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( v8_pre_topc(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( v2_pre_topc(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])])).

fof(c_0_31,plain,(
    ! [X39,X40,X41] :
      ( ( m1_subset_1(esk8_3(X39,X40,X41),u1_struct_0(X39))
        | ~ v10_waybel_0(X41,X39)
        | ~ r3_waybel_9(X39,X41,X40)
        | X40 = k1_waybel_2(X39,X41)
        | v2_struct_0(X41)
        | ~ v4_orders_2(X41)
        | ~ v7_waybel_0(X41)
        | ~ l1_waybel_0(X41,X39)
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | ~ v2_pre_topc(X39)
        | ~ v8_pre_topc(X39)
        | ~ v3_orders_2(X39)
        | ~ v4_orders_2(X39)
        | ~ v5_orders_2(X39)
        | ~ v1_lattice3(X39)
        | ~ v2_lattice3(X39)
        | ~ v1_compts_1(X39)
        | ~ l1_waybel_9(X39) )
      & ( ~ v5_pre_topc(k4_waybel_1(X39,esk8_3(X39,X40,X41)),X39,X39)
        | ~ v10_waybel_0(X41,X39)
        | ~ r3_waybel_9(X39,X41,X40)
        | X40 = k1_waybel_2(X39,X41)
        | v2_struct_0(X41)
        | ~ v4_orders_2(X41)
        | ~ v7_waybel_0(X41)
        | ~ l1_waybel_0(X41,X39)
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | ~ v2_pre_topc(X39)
        | ~ v8_pre_topc(X39)
        | ~ v3_orders_2(X39)
        | ~ v4_orders_2(X39)
        | ~ v5_orders_2(X39)
        | ~ v1_lattice3(X39)
        | ~ v2_lattice3(X39)
        | ~ v1_compts_1(X39)
        | ~ l1_waybel_9(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_waybel_9])])])])])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk5_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ l1_pre_topc(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29]),c_0_30])).

cnf(c_0_33,plain,
    ( l1_pre_topc(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,plain,
    ( r3_waybel_9(X1,X2,esk5_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_35,plain,(
    ! [X20,X21,X22,X23] :
      ( ( m1_subset_1(esk3_4(X20,X21,X22,X23),u1_struct_0(X20))
        | X22 != X23
        | ~ v10_waybel_0(X21,X20)
        | ~ r3_waybel_9(X20,X21,X22)
        | r2_lattice3(X20,k2_relset_1(u1_struct_0(X21),u1_struct_0(X20),u1_waybel_0(X20,X21)),X23)
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | v2_struct_0(X21)
        | ~ v4_orders_2(X21)
        | ~ v7_waybel_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | ~ v2_pre_topc(X20)
        | ~ v8_pre_topc(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ v1_lattice3(X20)
        | ~ v2_lattice3(X20)
        | ~ v1_compts_1(X20)
        | ~ l1_waybel_9(X20) )
      & ( ~ v5_pre_topc(k4_waybel_1(X20,esk3_4(X20,X21,X22,X23)),X20,X20)
        | X22 != X23
        | ~ v10_waybel_0(X21,X20)
        | ~ r3_waybel_9(X20,X21,X22)
        | r2_lattice3(X20,k2_relset_1(u1_struct_0(X21),u1_struct_0(X20),u1_waybel_0(X20,X21)),X23)
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | v2_struct_0(X21)
        | ~ v4_orders_2(X21)
        | ~ v7_waybel_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | ~ v2_pre_topc(X20)
        | ~ v8_pre_topc(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ v1_lattice3(X20)
        | ~ v2_lattice3(X20)
        | ~ v1_compts_1(X20)
        | ~ l1_waybel_9(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l48_waybel_9])])])])])])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk8_3(X1,X2,X3),u1_struct_0(X1))
    | X2 = k1_waybel_2(X1,X3)
    | v2_struct_0(X3)
    | ~ v10_waybel_0(X3,X1)
    | ~ r3_waybel_9(X1,X3,X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk5_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_18])])).

cnf(c_0_38,negated_conjecture,
    ( v2_lattice3(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( v4_orders_2(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( v5_orders_2(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( v3_orders_2(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( r3_waybel_9(esk9_0,esk10_0,esk5_2(esk9_0,esk10_0))
    | ~ l1_pre_topc(esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29]),c_0_30])).

cnf(c_0_43,plain,
    ( X2 = k1_waybel_2(X1,X3)
    | v2_struct_0(X3)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk8_3(X1,X2,X3)),X1,X1)
    | ~ v10_waybel_0(X3,X1)
    | ~ r3_waybel_9(X1,X3,X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X1))
    | r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)
    | v2_struct_0(X2)
    | X3 != X4
    | ~ v10_waybel_0(X2,X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_45,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( m1_subset_1(esk1_2(X10,X11),u1_struct_0(X10))
        | ~ r1_yellow_0(X10,X11)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r2_lattice3(X10,X11,esk1_2(X10,X11))
        | ~ r1_yellow_0(X10,X11)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_lattice3(X10,X11,X13)
        | r1_orders_2(X10,esk1_2(X10,X11),X13)
        | ~ r1_yellow_0(X10,X11)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk2_3(X10,X14,X15),u1_struct_0(X10))
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r2_lattice3(X10,X14,X15)
        | r1_yellow_0(X10,X14)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r2_lattice3(X10,X14,esk2_3(X10,X14,X15))
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r2_lattice3(X10,X14,X15)
        | r1_yellow_0(X10,X14)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,X15,esk2_3(X10,X14,X15))
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r2_lattice3(X10,X14,X15)
        | r1_yellow_0(X10,X14)
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_yellow_0])])])])])])).

cnf(c_0_46,negated_conjecture,
    ( esk5_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,X1)
    | m1_subset_1(esk8_3(esk9_0,esk5_2(esk9_0,esk10_0),X1),u1_struct_0(esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ v10_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_47,negated_conjecture,
    ( v10_waybel_0(esk10_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_48,negated_conjecture,
    ( r3_waybel_9(esk9_0,esk10_0,esk5_2(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_33]),c_0_18])])).

cnf(c_0_49,negated_conjecture,
    ( esk5_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ v10_waybel_0(X1,esk9_0)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk5_2(esk9_0,esk10_0),X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_37]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_50,plain,
    ( r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)
    | m1_subset_1(esk3_4(X1,X2,X3,X3),u1_struct_0(X1))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ v10_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v1_compts_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_9(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,X1),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_53,negated_conjecture,
    ( esk5_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk5_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_24]),c_0_26]),c_0_23])]),c_0_29])).

cnf(c_0_54,negated_conjecture,
    ( esk5_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk5_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_47]),c_0_48]),c_0_24]),c_0_26]),c_0_23])]),c_0_29])).

cnf(c_0_55,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X1)),esk5_2(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,X1,esk5_2(esk9_0,esk10_0),esk5_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ v10_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_37]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

fof(c_0_56,plain,(
    ! [X34,X35,X38] :
      ( ( m1_subset_1(esk6_2(X34,X35),u1_struct_0(X34))
        | ~ m1_subset_1(X38,u1_struct_0(X34))
        | ~ r3_waybel_9(X34,X35,X38)
        | r2_hidden(X38,k10_yellow_6(X34,X35))
        | v2_struct_0(X35)
        | ~ v4_orders_2(X35)
        | ~ v7_waybel_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ v8_pre_topc(X34)
        | ~ v1_compts_1(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_subset_1(esk7_2(X34,X35),u1_struct_0(X34))
        | ~ m1_subset_1(X38,u1_struct_0(X34))
        | ~ r3_waybel_9(X34,X35,X38)
        | r2_hidden(X38,k10_yellow_6(X34,X35))
        | v2_struct_0(X35)
        | ~ v4_orders_2(X35)
        | ~ v7_waybel_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ v8_pre_topc(X34)
        | ~ v1_compts_1(X34)
        | ~ l1_pre_topc(X34) )
      & ( r3_waybel_9(X34,X35,esk6_2(X34,X35))
        | ~ m1_subset_1(X38,u1_struct_0(X34))
        | ~ r3_waybel_9(X34,X35,X38)
        | r2_hidden(X38,k10_yellow_6(X34,X35))
        | v2_struct_0(X35)
        | ~ v4_orders_2(X35)
        | ~ v7_waybel_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ v8_pre_topc(X34)
        | ~ v1_compts_1(X34)
        | ~ l1_pre_topc(X34) )
      & ( r3_waybel_9(X34,X35,esk7_2(X34,X35))
        | ~ m1_subset_1(X38,u1_struct_0(X34))
        | ~ r3_waybel_9(X34,X35,X38)
        | r2_hidden(X38,k10_yellow_6(X34,X35))
        | v2_struct_0(X35)
        | ~ v4_orders_2(X35)
        | ~ v7_waybel_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ v8_pre_topc(X34)
        | ~ v1_compts_1(X34)
        | ~ l1_pre_topc(X34) )
      & ( esk6_2(X34,X35) != esk7_2(X34,X35)
        | ~ m1_subset_1(X38,u1_struct_0(X34))
        | ~ r3_waybel_9(X34,X35,X38)
        | r2_hidden(X38,k10_yellow_6(X34,X35))
        | v2_struct_0(X35)
        | ~ v4_orders_2(X35)
        | ~ v7_waybel_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ v8_pre_topc(X34)
        | ~ v1_compts_1(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t33_waybel_9])])])])])])).

cnf(c_0_57,negated_conjecture,
    ( r1_yellow_0(esk9_0,X1)
    | m1_subset_1(esk2_3(esk9_0,X1,esk5_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r2_lattice3(esk9_0,X1,esk5_2(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_37]),c_0_40]),c_0_21])])).

cnf(c_0_58,negated_conjecture,
    ( esk5_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk5_2(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,esk5_2(esk9_0,esk10_0),esk5_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_47]),c_0_48]),c_0_24]),c_0_26]),c_0_23])]),c_0_29])).

cnf(c_0_60,plain,
    ( m1_subset_1(esk7_2(X1,X2),u1_struct_0(X1))
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,plain,
    ( r2_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_62,plain,(
    ! [X17,X18] :
      ( ( ~ r1_waybel_9(X17,X18)
        | r1_yellow_0(X17,k2_relset_1(u1_struct_0(X18),u1_struct_0(X17),u1_waybel_0(X17,X18)))
        | ~ l1_waybel_0(X18,X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r1_yellow_0(X17,k2_relset_1(u1_struct_0(X18),u1_struct_0(X17),u1_waybel_0(X17,X18)))
        | r1_waybel_9(X17,X18)
        | ~ l1_waybel_0(X18,X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_waybel_9])])])])).

cnf(c_0_63,negated_conjecture,
    ( r1_yellow_0(esk9_0,X1)
    | m1_subset_1(esk2_3(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r2_lattice3(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58]),c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_58]),c_0_58]),c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))
    | m1_subset_1(esk7_2(esk9_0,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(esk9_0)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_37]),c_0_25]),c_0_27]),c_0_28])]),c_0_30])).

cnf(c_0_66,negated_conjecture,
    ( r2_lattice3(esk9_0,X1,esk2_3(esk9_0,X1,esk5_2(esk9_0,esk10_0)))
    | r1_yellow_0(esk9_0,X1)
    | ~ r2_lattice3(esk9_0,X1,esk5_2(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_37]),c_0_40]),c_0_21])])).

cnf(c_0_67,plain,
    ( r1_waybel_9(X1,X2)
    | ~ r1_yellow_0(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))
    | m1_subset_1(esk7_2(esk9_0,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_33]),c_0_18])])).

cnf(c_0_70,negated_conjecture,
    ( r2_lattice3(esk9_0,X1,esk2_3(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0)))
    | r1_yellow_0(esk9_0,X1)
    | ~ r2_lattice3(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_58]),c_0_58])).

cnf(c_0_71,plain,
    ( m1_subset_1(esk6_2(X1,X2),u1_struct_0(X1))
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_72,plain,(
    ! [X25,X26,X27,X28,X30] :
      ( ( m1_subset_1(esk4_4(X25,X26,X27,X28),u1_struct_0(X25))
        | X27 != X28
        | ~ r3_waybel_9(X25,X26,X27)
        | ~ m1_subset_1(X30,u1_struct_0(X25))
        | ~ r2_lattice3(X25,k2_relset_1(u1_struct_0(X26),u1_struct_0(X25),u1_waybel_0(X25,X26)),X30)
        | r3_orders_2(X25,X28,X30)
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | v2_struct_0(X26)
        | ~ v4_orders_2(X26)
        | ~ v7_waybel_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | ~ v2_pre_topc(X25)
        | ~ v8_pre_topc(X25)
        | ~ v3_orders_2(X25)
        | ~ v4_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ v1_lattice3(X25)
        | ~ v2_lattice3(X25)
        | ~ v1_compts_1(X25)
        | ~ l1_waybel_9(X25) )
      & ( ~ v5_pre_topc(k4_waybel_1(X25,esk4_4(X25,X26,X27,X28)),X25,X25)
        | X27 != X28
        | ~ r3_waybel_9(X25,X26,X27)
        | ~ m1_subset_1(X30,u1_struct_0(X25))
        | ~ r2_lattice3(X25,k2_relset_1(u1_struct_0(X26),u1_struct_0(X25),u1_waybel_0(X25,X26)),X30)
        | r3_orders_2(X25,X28,X30)
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | v2_struct_0(X26)
        | ~ v4_orders_2(X26)
        | ~ v7_waybel_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | ~ v2_pre_topc(X25)
        | ~ v8_pre_topc(X25)
        | ~ v3_orders_2(X25)
        | ~ v4_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ v1_lattice3(X25)
        | ~ v2_lattice3(X25)
        | ~ v1_compts_1(X25)
        | ~ l1_waybel_9(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l49_waybel_9])])])])])])).

cnf(c_0_73,negated_conjecture,
    ( ~ r1_waybel_9(esk9_0,esk10_0)
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_74,negated_conjecture,
    ( r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_23]),c_0_21])])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_23]),c_0_48]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_76,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_64])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))
    | m1_subset_1(esk6_2(esk9_0,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(esk9_0)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_37]),c_0_25]),c_0_27]),c_0_28])]),c_0_30])).

cnf(c_0_78,plain,
    ( m1_subset_1(esk4_4(X1,X2,X3,X4),u1_struct_0(X1))
    | r3_orders_2(X1,X4,X5)
    | v2_struct_0(X2)
    | X3 != X4
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(rw,[status(thm)],[c_0_75,c_0_58])).

cnf(c_0_81,negated_conjecture,
    ( r1_waybel_9(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_76]),c_0_23]),c_0_21])])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))
    | m1_subset_1(esk6_2(esk9_0,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_33]),c_0_18])])).

fof(c_0_83,plain,(
    ! [X6,X7,X8] :
      ( ( ~ r3_orders_2(X6,X7,X8)
        | r1_orders_2(X6,X7,X8)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ m1_subset_1(X8,u1_struct_0(X6)) )
      & ( ~ r1_orders_2(X6,X7,X8)
        | r3_orders_2(X6,X7,X8)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ m1_subset_1(X8,u1_struct_0(X6)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_84,plain,
    ( r3_orders_2(X1,X2,X3)
    | m1_subset_1(esk4_4(X1,X4,X2,X2),u1_struct_0(X1))
    | v2_struct_0(X4)
    | ~ r3_waybel_9(X1,X4,X2)
    | ~ v7_waybel_0(X4)
    | ~ v1_compts_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v4_orders_2(X4)
    | ~ v4_orders_2(X1)
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_9(X1)
    | ~ l1_waybel_0(X4,X1)
    | ~ r2_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_23]),c_0_48]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_88,plain,
    ( r1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk2_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_89,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_91,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_80])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(rw,[status(thm)],[c_0_87,c_0_58])).

cnf(c_0_93,negated_conjecture,
    ( r1_yellow_0(esk9_0,X1)
    | ~ r2_lattice3(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ r1_orders_2(esk9_0,esk5_2(esk9_0,esk10_0),esk2_3(esk9_0,X1,esk5_2(esk9_0,esk10_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_37]),c_0_40]),c_0_21])])).

cnf(c_0_94,negated_conjecture,
    ( r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_85]),c_0_21]),c_0_41])]),c_0_30])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(k1_waybel_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_58])).

cnf(c_0_96,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_23]),c_0_24]),c_0_26])]),c_0_29]),c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( r3_waybel_9(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_58])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( r1_yellow_0(esk9_0,X1)
    | ~ r2_lattice3(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0))
    | ~ r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_58]),c_0_58]),c_0_58])).

cnf(c_0_100,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_95])])).

cnf(c_0_102,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_98]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_103,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_92])).

cnf(c_0_104,plain,
    ( r3_orders_2(X1,X4,X5)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk4_4(X1,X2,X3,X4)),X1,X1)
    | X3 != X4
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_105,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_64])).

cnf(c_0_106,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_98]),c_0_21]),c_0_41])]),c_0_30])).

cnf(c_0_108,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_23]),c_0_24]),c_0_26])]),c_0_29]),c_0_103])).

cnf(c_0_109,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X4)
    | ~ r3_waybel_9(X1,X4,X2)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk4_4(X1,X4,X2,X2)),X1,X1)
    | ~ v7_waybel_0(X4)
    | ~ v1_compts_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v4_orders_2(X4)
    | ~ v4_orders_2(X1)
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_9(X1)
    | ~ l1_waybel_0(X4,X1)
    | ~ r2_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_107,c_0_95])).

cnf(c_0_112,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_97]),c_0_95])])).

cnf(c_0_113,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_85]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_114,negated_conjecture,
    ( r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_110]),c_0_23]),c_0_21])])).

cnf(c_0_115,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_116,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_23]),c_0_24]),c_0_26])]),c_0_29]),c_0_91])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_114]),c_0_80])).

cnf(c_0_118,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_115])).

cnf(c_0_119,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_97]),c_0_95])])).

cnf(c_0_120,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_117])).

cnf(c_0_121,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_98]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_122,negated_conjecture,
    ( r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_118]),c_0_23]),c_0_21])])).

cnf(c_0_123,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_124,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_23]),c_0_24]),c_0_26])]),c_0_29]),c_0_103])).

cnf(c_0_125,negated_conjecture,
    ( m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_122]),c_0_92])).

cnf(c_0_126,plain,
    ( r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X2,X3,X4)),X1,X1)
    | X3 != X4
    | ~ v10_waybel_0(X2,X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_127,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_123])).

cnf(c_0_128,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_97]),c_0_95])])).

cnf(c_0_129,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_125])).

cnf(c_0_130,plain,
    ( r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ v10_waybel_0(X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X2,X3,X3)),X1,X1)
    | ~ v7_waybel_0(X2)
    | ~ v1_compts_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_9(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_126])).

cnf(c_0_131,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_127])).

cnf(c_0_132,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_133,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X1)),esk5_2(esk9_0,esk10_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ v10_waybel_0(X1,esk9_0)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,X1,esk5_2(esk9_0,esk10_0),esk5_2(esk9_0,esk10_0))),esk9_0,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_37]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_134,negated_conjecture,
    ( r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_131]),c_0_23]),c_0_21])])).

cnf(c_0_135,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_132])).

cnf(c_0_136,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X1)),k1_waybel_2(esk9_0,esk10_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0))
    | ~ v10_waybel_0(X1,esk9_0)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_58]),c_0_58]),c_0_58]),c_0_58])).

cnf(c_0_137,negated_conjecture,
    ( m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_134]),c_0_80])).

cnf(c_0_138,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_135])).

cnf(c_0_139,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_47]),c_0_97]),c_0_24]),c_0_26]),c_0_23])]),c_0_29])).

cnf(c_0_140,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_137])).

cnf(c_0_141,negated_conjecture,
    ( r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_138]),c_0_23]),c_0_21])])).

cnf(c_0_142,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_143,negated_conjecture,
    ( m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_141]),c_0_92])).

cnf(c_0_144,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_142])).

cnf(c_0_145,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_143])).

cnf(c_0_146,negated_conjecture,
    ( r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_144]),c_0_23]),c_0_21])])).

cnf(c_0_147,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_142])).

cnf(c_0_148,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_145])).

cnf(c_0_149,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_146]),c_0_80])).

cnf(c_0_150,negated_conjecture,
    ( r1_waybel_9(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_147]),c_0_23]),c_0_21])])).

cnf(c_0_151,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_148])).

cnf(c_0_152,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_149]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_153,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_150]),c_0_80])).

cnf(c_0_154,negated_conjecture,
    ( r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_151]),c_0_23]),c_0_21])])).

cnf(c_0_155,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_148])).

cnf(c_0_156,negated_conjecture,
    ( r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_149]),c_0_21]),c_0_41])]),c_0_30])).

cnf(c_0_157,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_23]),c_0_24]),c_0_26])]),c_0_29]),c_0_153])).

cnf(c_0_158,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_154]),c_0_92])).

cnf(c_0_159,negated_conjecture,
    ( r1_waybel_9(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_155]),c_0_23]),c_0_21])])).

cnf(c_0_160,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_156,c_0_95])).

cnf(c_0_161,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_97]),c_0_95])])).

cnf(c_0_162,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_158]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_163,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_159]),c_0_92])).

cnf(c_0_164,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_142])).

cnf(c_0_165,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_160,c_0_161])).

cnf(c_0_166,negated_conjecture,
    ( r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_158]),c_0_21]),c_0_41])]),c_0_30])).

cnf(c_0_167,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_23]),c_0_24]),c_0_26])]),c_0_29]),c_0_163])).

cnf(c_0_168,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_164,c_0_165])).

cnf(c_0_169,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_166,c_0_95])).

cnf(c_0_170,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_97]),c_0_95])])).

cnf(c_0_171,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_149]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_172,negated_conjecture,
    ( r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_168]),c_0_23]),c_0_21])])).

cnf(c_0_173,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_148])).

cnf(c_0_174,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_169,c_0_170])).

cnf(c_0_175,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_23]),c_0_24]),c_0_26])]),c_0_29]),c_0_153])).

cnf(c_0_176,negated_conjecture,
    ( m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_172]),c_0_80])).

cnf(c_0_177,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_173,c_0_174])).

cnf(c_0_178,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_97]),c_0_95])])).

cnf(c_0_179,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_176])).

cnf(c_0_180,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_158]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_181,negated_conjecture,
    ( r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_177]),c_0_23]),c_0_21])])).

cnf(c_0_182,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_178,c_0_179])).

cnf(c_0_183,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_23]),c_0_24]),c_0_26])]),c_0_29]),c_0_163])).

cnf(c_0_184,negated_conjecture,
    ( m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_181]),c_0_92])).

cnf(c_0_185,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_160,c_0_182])).

cnf(c_0_186,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_97]),c_0_95])])).

cnf(c_0_187,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_184])).

cnf(c_0_188,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_164,c_0_185])).

cnf(c_0_189,plain,
    ( r3_waybel_9(X1,X2,esk7_2(X1,X2))
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_190,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_186,c_0_187])).

cnf(c_0_191,negated_conjecture,
    ( r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_188]),c_0_23]),c_0_21])])).

cnf(c_0_192,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))
    | r3_waybel_9(esk9_0,X1,esk7_2(esk9_0,X1))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(esk9_0)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189,c_0_95]),c_0_25]),c_0_27]),c_0_28])]),c_0_30])).

cnf(c_0_193,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_169,c_0_190])).

cnf(c_0_194,negated_conjecture,
    ( m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_191]),c_0_80])).

cnf(c_0_195,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))
    | r3_waybel_9(esk9_0,X1,esk7_2(esk9_0,X1))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_33]),c_0_18])])).

cnf(c_0_196,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_173,c_0_193])).

cnf(c_0_197,plain,
    ( r3_waybel_9(X1,X2,esk6_2(X1,X2))
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_198,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,X1)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),X1),u1_struct_0(esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk7_2(esk9_0,esk10_0))
    | ~ v10_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_194]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_199,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_195,c_0_23]),c_0_97]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_200,negated_conjecture,
    ( r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_196]),c_0_23]),c_0_21])])).

cnf(c_0_201,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))
    | r3_waybel_9(esk9_0,X1,esk6_2(esk9_0,X1))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(esk9_0)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197,c_0_95]),c_0_25]),c_0_27]),c_0_28])]),c_0_30])).

cnf(c_0_202,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_47]),c_0_24]),c_0_26]),c_0_23])]),c_0_29])).

cnf(c_0_203,negated_conjecture,
    ( r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_199])).

cnf(c_0_204,negated_conjecture,
    ( m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_200]),c_0_92])).

cnf(c_0_205,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))
    | r3_waybel_9(esk9_0,X1,esk6_2(esk9_0,X1))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201,c_0_33]),c_0_18])])).

cnf(c_0_206,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_202,c_0_203])).

cnf(c_0_207,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,X1)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),X1),u1_struct_0(esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk6_2(esk9_0,esk10_0))
    | ~ v10_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_204]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_208,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205,c_0_23]),c_0_97]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_209,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_206]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_210,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_207,c_0_47]),c_0_24]),c_0_26]),c_0_23])]),c_0_29])).

cnf(c_0_211,negated_conjecture,
    ( r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_208])).

cnf(c_0_212,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_209,c_0_23]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_213,negated_conjecture,
    ( r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_199])).

cnf(c_0_214,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_210,c_0_211])).

cnf(c_0_215,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_206]),c_0_21]),c_0_41])]),c_0_30])).

cnf(c_0_216,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_212,c_0_213]),c_0_202])).

cnf(c_0_217,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_214]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_218,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_215,c_0_95])).

cnf(c_0_219,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_216,c_0_97]),c_0_95])])).

cnf(c_0_220,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_217,c_0_23]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_221,negated_conjecture,
    ( r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_208])).

cnf(c_0_222,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_218,c_0_219])).

cnf(c_0_223,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_214]),c_0_21]),c_0_41])]),c_0_30])).

cnf(c_0_224,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_220,c_0_221]),c_0_210])).

cnf(c_0_225,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_222])).

cnf(c_0_226,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_223,c_0_95])).

cnf(c_0_227,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_224,c_0_97]),c_0_95])])).

cnf(c_0_228,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_206]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_229,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_225]),c_0_23]),c_0_21])])).

cnf(c_0_230,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_226,c_0_227])).

cnf(c_0_231,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_228,c_0_23]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_232,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_229])).

cnf(c_0_233,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_230])).

cnf(c_0_234,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_231,c_0_213]),c_0_202])).

cnf(c_0_235,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_232,c_0_199]),c_0_202])).

cnf(c_0_236,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_214]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_237,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_233]),c_0_23]),c_0_21])])).

cnf(c_0_238,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_234,c_0_97]),c_0_95])])).

cnf(c_0_239,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_235])).

cnf(c_0_240,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_236,c_0_23]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_241,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_237])).

cnf(c_0_242,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_238,c_0_239])).

cnf(c_0_243,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_240,c_0_221]),c_0_210])).

cnf(c_0_244,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_241,c_0_208]),c_0_210])).

cnf(c_0_245,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_218,c_0_242])).

cnf(c_0_246,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_97]),c_0_95])])).

cnf(c_0_247,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_244])).

cnf(c_0_248,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_245])).

cnf(c_0_249,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_246,c_0_247])).

cnf(c_0_250,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_248]),c_0_23]),c_0_21])])).

cnf(c_0_251,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_226,c_0_249])).

cnf(c_0_252,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_250])).

cnf(c_0_253,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_251])).

cnf(c_0_254,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_252,c_0_199]),c_0_202])).

cnf(c_0_255,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_253]),c_0_23]),c_0_21])])).

cnf(c_0_256,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_254])).

cnf(c_0_257,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_255])).

cnf(c_0_258,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_256])).

cnf(c_0_259,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_257,c_0_208]),c_0_210])).

cnf(c_0_260,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_258])).

cnf(c_0_261,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_259])).

cnf(c_0_262,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_260]),c_0_23]),c_0_21])])).

cnf(c_0_263,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_258])).

cnf(c_0_264,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_261])).

cnf(c_0_265,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_262])).

cnf(c_0_266,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_waybel_9(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_263]),c_0_23]),c_0_21])])).

cnf(c_0_267,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_264])).

cnf(c_0_268,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_265,c_0_199]),c_0_202])).

cnf(c_0_269,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_266])).

cnf(c_0_270,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_267]),c_0_23]),c_0_21])])).

cnf(c_0_271,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_264])).

cnf(c_0_272,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_268]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_273,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_269,c_0_199]),c_0_202])).

cnf(c_0_274,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_270])).

cnf(c_0_275,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_waybel_9(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_271]),c_0_23]),c_0_21])])).

cnf(c_0_276,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_268]),c_0_21]),c_0_41])]),c_0_30])).

cnf(c_0_277,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_272,c_0_23]),c_0_24]),c_0_26])]),c_0_29]),c_0_273])).

cnf(c_0_278,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_274,c_0_208]),c_0_210])).

cnf(c_0_279,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_275])).

cnf(c_0_280,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_276,c_0_95])).

cnf(c_0_281,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_277,c_0_97]),c_0_95])])).

cnf(c_0_282,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_278]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_283,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_279,c_0_208]),c_0_210])).

cnf(c_0_284,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_258])).

cnf(c_0_285,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_280,c_0_281])).

cnf(c_0_286,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_278]),c_0_21]),c_0_41])]),c_0_30])).

cnf(c_0_287,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_282,c_0_23]),c_0_24]),c_0_26])]),c_0_29]),c_0_283])).

cnf(c_0_288,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_284,c_0_285])).

cnf(c_0_289,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_286,c_0_95])).

cnf(c_0_290,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_287,c_0_97]),c_0_95])])).

cnf(c_0_291,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_288]),c_0_23]),c_0_21])])).

cnf(c_0_292,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_264])).

cnf(c_0_293,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_289,c_0_290])).

cnf(c_0_294,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_268]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_295,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_291])).

cnf(c_0_296,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_292,c_0_293])).

cnf(c_0_297,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_294,c_0_23]),c_0_24]),c_0_26])]),c_0_29]),c_0_273])).

cnf(c_0_298,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_295,c_0_199]),c_0_202])).

cnf(c_0_299,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_296]),c_0_23]),c_0_21])])).

cnf(c_0_300,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_297,c_0_97]),c_0_95])])).

cnf(c_0_301,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_298])).

cnf(c_0_302,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_278]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_303,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_299])).

cnf(c_0_304,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_300,c_0_301])).

cnf(c_0_305,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_302,c_0_23]),c_0_24]),c_0_26])]),c_0_29]),c_0_283])).

cnf(c_0_306,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_303,c_0_208]),c_0_210])).

cnf(c_0_307,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_280,c_0_304])).

cnf(c_0_308,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_305,c_0_97]),c_0_95])])).

cnf(c_0_309,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_306])).

cnf(c_0_310,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_284,c_0_307])).

cnf(c_0_311,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_308,c_0_309])).

cnf(c_0_312,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_310]),c_0_23]),c_0_21])])).

cnf(c_0_313,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_289,c_0_311])).

cnf(c_0_314,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk7_2(esk9_0,esk10_0))
    | ~ v10_waybel_0(X1,esk9_0)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_194]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_315,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_312])).

cnf(c_0_316,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_292,c_0_313])).

cnf(c_0_317,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | ~ r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_314,c_0_47]),c_0_24]),c_0_26]),c_0_23])]),c_0_29])).

cnf(c_0_318,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_315,c_0_199]),c_0_202])).

cnf(c_0_319,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_316]),c_0_23]),c_0_21])])).

cnf(c_0_320,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_317,c_0_203])).

cnf(c_0_321,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_318])).

cnf(c_0_322,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk6_2(esk9_0,esk10_0))
    | ~ v10_waybel_0(X1,esk9_0)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_204]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_323,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_319])).

cnf(c_0_324,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_320,c_0_321])).

cnf(c_0_325,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | ~ r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_322,c_0_47]),c_0_24]),c_0_26]),c_0_23])]),c_0_29])).

cnf(c_0_326,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_323,c_0_208]),c_0_210])).

cnf(c_0_327,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_324]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_328,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_325,c_0_211])).

cnf(c_0_329,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_326])).

cnf(c_0_330,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_327,c_0_23]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_331,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_328,c_0_329])).

cnf(c_0_332,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_324]),c_0_21]),c_0_41])]),c_0_30])).

cnf(c_0_333,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_330,c_0_213])).

cnf(c_0_334,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_331]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_335,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_332,c_0_95])).

cnf(c_0_336,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_333,c_0_97]),c_0_95])])).

cnf(c_0_337,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_334,c_0_23]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_338,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_335,c_0_336])).

cnf(c_0_339,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_331]),c_0_21]),c_0_41])]),c_0_30])).

cnf(c_0_340,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_337,c_0_221])).

cnf(c_0_341,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_338])).

cnf(c_0_342,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_339,c_0_95])).

cnf(c_0_343,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_340,c_0_97]),c_0_95])])).

cnf(c_0_344,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_324]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_345,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_341]),c_0_23]),c_0_21])])).

cnf(c_0_346,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_342,c_0_343])).

cnf(c_0_347,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_344,c_0_23]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_348,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_345]),c_0_199])).

cnf(c_0_349,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_346])).

cnf(c_0_350,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_347,c_0_213])).

cnf(c_0_351,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_317,c_0_348]),c_0_321])).

cnf(c_0_352,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_331]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_353,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_349]),c_0_23]),c_0_21])])).

cnf(c_0_354,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_350,c_0_97]),c_0_95])])).

cnf(c_0_355,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_351])).

cnf(c_0_356,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_352,c_0_23]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_357,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_353]),c_0_208])).

cnf(c_0_358,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_354,c_0_355])).

cnf(c_0_359,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_356,c_0_221])).

cnf(c_0_360,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_325,c_0_357]),c_0_329])).

cnf(c_0_361,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_335,c_0_358])).

cnf(c_0_362,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_359,c_0_97]),c_0_95])])).

cnf(c_0_363,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_360])).

cnf(c_0_364,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_361])).

cnf(c_0_365,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_362,c_0_363])).

cnf(c_0_366,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_364]),c_0_23]),c_0_21])])).

cnf(c_0_367,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_342,c_0_365])).

cnf(c_0_368,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_366]),c_0_199])).

cnf(c_0_369,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_367])).

cnf(c_0_370,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_317,c_0_368]),c_0_321])).

cnf(c_0_371,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_369]),c_0_23]),c_0_21])])).

cnf(c_0_372,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_370])).

cnf(c_0_373,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_371]),c_0_208])).

cnf(c_0_374,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_372])).

cnf(c_0_375,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_325,c_0_373]),c_0_329])).

cnf(c_0_376,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_374])).

cnf(c_0_377,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_375])).

cnf(c_0_378,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_376]),c_0_23]),c_0_21])])).

cnf(c_0_379,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_377])).

cnf(c_0_380,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_378])).

cnf(c_0_381,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_379])).

cnf(c_0_382,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_380,c_0_199])).

cnf(c_0_383,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_374])).

cnf(c_0_384,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_381]),c_0_23]),c_0_21])])).

cnf(c_0_385,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_317,c_0_382]),c_0_321])).

cnf(c_0_386,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_waybel_9(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_383]),c_0_23]),c_0_21])])).

cnf(c_0_387,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_384])).

cnf(c_0_388,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_385]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_389,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_386])).

cnf(c_0_390,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_387,c_0_208])).

cnf(c_0_391,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_379])).

cnf(c_0_392,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_388,c_0_23]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_393,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_389,c_0_199])).

cnf(c_0_394,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_325,c_0_390]),c_0_329])).

cnf(c_0_395,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_waybel_9(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_391]),c_0_23]),c_0_21])])).

cnf(c_0_396,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_385]),c_0_21]),c_0_41])]),c_0_30])).

cnf(c_0_397,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_392,c_0_393])).

cnf(c_0_398,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_394]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_399,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_395])).

cnf(c_0_400,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_396,c_0_95])).

cnf(c_0_401,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_397,c_0_97]),c_0_95])])).

cnf(c_0_402,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_398,c_0_23]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_403,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_399,c_0_208])).

cnf(c_0_404,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | ~ r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_374])).

cnf(c_0_405,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_400,c_0_401])).

cnf(c_0_406,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_394]),c_0_21]),c_0_41])]),c_0_30])).

cnf(c_0_407,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_402,c_0_403])).

cnf(c_0_408,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_404,c_0_405])).

cnf(c_0_409,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_406,c_0_95])).

cnf(c_0_410,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_407,c_0_97]),c_0_95])])).

cnf(c_0_411,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_385]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_412,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_408]),c_0_23]),c_0_21])])).

cnf(c_0_413,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | ~ r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_379])).

cnf(c_0_414,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_409,c_0_410])).

cnf(c_0_415,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_411,c_0_23]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_416,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_412]),c_0_199])).

cnf(c_0_417,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_413,c_0_414])).

cnf(c_0_418,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_415,c_0_393])).

cnf(c_0_419,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_317,c_0_416]),c_0_321])).

cnf(c_0_420,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_394]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_421,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_417]),c_0_23]),c_0_21])])).

cnf(c_0_422,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_418,c_0_95]),c_0_97])])).

cnf(c_0_423,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_419])).

cnf(c_0_424,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_420,c_0_23]),c_0_24]),c_0_26])]),c_0_29])).

cnf(c_0_425,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_421]),c_0_208])).

cnf(c_0_426,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_422,c_0_423])).

cnf(c_0_427,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_424,c_0_403])).

cnf(c_0_428,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_325,c_0_425]),c_0_329])).

cnf(c_0_429,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_400,c_0_426])).

cnf(c_0_430,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_427,c_0_95]),c_0_97])])).

cnf(c_0_431,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_428])).

cnf(c_0_432,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_404,c_0_429])).

cnf(c_0_433,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_430,c_0_431])).

cnf(c_0_434,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_waybel_9(esk9_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_432]),c_0_23]),c_0_21])])).

cnf(c_0_435,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_409,c_0_433])).

cnf(c_0_436,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_434]),c_0_199])).

cnf(c_0_437,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_413,c_0_435])).

cnf(c_0_438,plain,
    ( r2_hidden(X3,k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | esk6_2(X1,X2) != esk7_2(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_439,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_317,c_0_436]),c_0_321])).

cnf(c_0_440,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_waybel_9(esk9_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_437]),c_0_23]),c_0_21])])).

cnf(c_0_441,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk9_0,esk10_0))
    | esk6_2(esk9_0,esk10_0) != k1_waybel_2(esk9_0,esk10_0)
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ l1_pre_topc(esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_438,c_0_439]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_23])]),c_0_29]),c_0_30])).

cnf(c_0_442,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_440]),c_0_208])).

cnf(c_0_443,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk9_0,esk10_0))
    | esk6_2(esk9_0,esk10_0) != k1_waybel_2(esk9_0,esk10_0)
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_441,c_0_33]),c_0_18])])).

cnf(c_0_444,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_2(esk9_0,esk10_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_325,c_0_442]),c_0_329])).

cnf(c_0_445,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk9_0,esk10_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_443,c_0_444])])).

cnf(c_0_446,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_445,c_0_97]),c_0_95])])).

cnf(c_0_447,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_446])])).

cnf(c_0_448,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_447]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_449,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_446])])).

cnf(c_0_450,negated_conjecture,
    ( r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_447]),c_0_21]),c_0_41])]),c_0_30])).

cnf(c_0_451,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_448,c_0_23]),c_0_24]),c_0_26])]),c_0_29]),c_0_449])).

cnf(c_0_452,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_450,c_0_95])).

cnf(c_0_453,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_451,c_0_97]),c_0_95])])).

cnf(c_0_454,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_452,c_0_453])).

cnf(c_0_455,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_447]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_456,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_454])).

cnf(c_0_457,negated_conjecture,
    ( ~ r1_waybel_9(esk9_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_446])])).

cnf(c_0_458,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_455,c_0_23]),c_0_24]),c_0_26])]),c_0_29]),c_0_449])).

cnf(c_0_459,negated_conjecture,
    ( m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_456]),c_0_23]),c_0_21])]),c_0_457])).

cnf(c_0_460,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_458,c_0_97]),c_0_95])])).

cnf(c_0_461,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_459])).

cnf(c_0_462,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_460,c_0_461])).

cnf(c_0_463,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_452,c_0_462])).

cnf(c_0_464,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_463])).

cnf(c_0_465,negated_conjecture,
    ( m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_464]),c_0_23]),c_0_21])]),c_0_457])).

cnf(c_0_466,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_465])).

cnf(c_0_467,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_466])])).

cnf(c_0_468,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_467])).

cnf(c_0_469,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_468]),c_0_23]),c_0_21])]),c_0_457])).

cnf(c_0_470,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_467])).

cnf(c_0_471,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_469]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_472,negated_conjecture,
    ( r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_470]),c_0_23]),c_0_21])]),c_0_457])).

cnf(c_0_473,negated_conjecture,
    ( r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_469]),c_0_21]),c_0_41])]),c_0_30])).

cnf(c_0_474,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_471,c_0_23]),c_0_24]),c_0_26]),c_0_472])]),c_0_29])).

cnf(c_0_475,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_473,c_0_95])).

cnf(c_0_476,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_474,c_0_97]),c_0_95])])).

cnf(c_0_477,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | ~ r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_467])).

cnf(c_0_478,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_475,c_0_476])).

cnf(c_0_479,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_469]),c_0_25]),c_0_38]),c_0_39]),c_0_27]),c_0_28]),c_0_18]),c_0_40]),c_0_16]),c_0_41])])).

cnf(c_0_480,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_477,c_0_478])).

cnf(c_0_481,negated_conjecture,
    ( r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_479,c_0_23]),c_0_24]),c_0_26]),c_0_472])]),c_0_29])).

cnf(c_0_482,negated_conjecture,
    ( m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_480]),c_0_23]),c_0_21])]),c_0_457])).

cnf(c_0_483,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_481,c_0_97]),c_0_95])])).

cnf(c_0_484,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_482])).

cnf(c_0_485,negated_conjecture,
    ( r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_483,c_0_484])])).

cnf(c_0_486,negated_conjecture,
    ( r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_475,c_0_485])])).

cnf(c_0_487,negated_conjecture,
    ( r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_477,c_0_486])])).

cnf(c_0_488,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_487]),c_0_23]),c_0_21])]),c_0_457]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:27:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.88/1.06  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.88/1.06  # and selection function SelectNewComplexAHP.
% 0.88/1.06  #
% 0.88/1.06  # Preprocessing time       : 0.030 s
% 0.88/1.06  # Presaturation interreduction done
% 0.88/1.06  
% 0.88/1.06  # Proof found!
% 0.88/1.06  # SZS status Theorem
% 0.88/1.06  # SZS output start CNFRefutation
% 0.88/1.06  fof(t38_waybel_9, conjecture, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>(![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X2),X1,X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v10_waybel_0(X2,X1)=>(r1_waybel_9(X1,X2)&r2_hidden(k1_waybel_2(X1,X2),k10_yellow_6(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_waybel_9)).
% 0.88/1.06  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.88/1.06  fof(dt_l1_waybel_9, axiom, ![X1]:(l1_waybel_9(X1)=>(l1_pre_topc(X1)&l1_orders_2(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 0.88/1.06  fof(t30_waybel_9, axiom, ![X1]:(((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&v1_compts_1(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&r3_waybel_9(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_waybel_9)).
% 0.88/1.06  fof(t35_waybel_9, axiom, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(((![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X4),X1,X1))&v10_waybel_0(X3,X1))&r3_waybel_9(X1,X3,X2))=>X2=k1_waybel_2(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_waybel_9)).
% 0.88/1.06  fof(l48_waybel_9, axiom, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((((X3=X4&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X5),X1,X1)))&v10_waybel_0(X2,X1))&r3_waybel_9(X1,X2,X3))=>r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l48_waybel_9)).
% 0.88/1.06  fof(t15_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(r1_yellow_0(X1,X2)<=>?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r2_lattice3(X1,X2,X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow_0)).
% 0.88/1.06  fof(t33_waybel_9, axiom, ![X1]:(((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&v1_compts_1(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r3_waybel_9(X1,X2,X3)&r3_waybel_9(X1,X2,X4))=>X3=X4)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)=>r2_hidden(X3,k10_yellow_6(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_waybel_9)).
% 0.88/1.06  fof(d3_waybel_9, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_waybel_0(X2,X1)=>(r1_waybel_9(X1,X2)<=>r1_yellow_0(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_waybel_9)).
% 0.88/1.06  fof(l49_waybel_9, axiom, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((X3=X4&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X5),X1,X1)))&r3_waybel_9(X1,X2,X3))=>![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)=>r3_orders_2(X1,X4,X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_waybel_9)).
% 0.88/1.06  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.88/1.06  fof(c_0_11, negated_conjecture, ~(![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>(![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X2),X1,X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v10_waybel_0(X2,X1)=>(r1_waybel_9(X1,X2)&r2_hidden(k1_waybel_2(X1,X2),k10_yellow_6(X1,X2)))))))), inference(assume_negation,[status(cth)],[t38_waybel_9])).
% 0.88/1.06  fof(c_0_12, plain, ![X9]:(~l1_orders_2(X9)|(~v1_lattice3(X9)|~v2_struct_0(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.88/1.06  fof(c_0_13, negated_conjecture, ![X44]:(((((((((v2_pre_topc(esk9_0)&v8_pre_topc(esk9_0))&v3_orders_2(esk9_0))&v4_orders_2(esk9_0))&v5_orders_2(esk9_0))&v1_lattice3(esk9_0))&v2_lattice3(esk9_0))&v1_compts_1(esk9_0))&l1_waybel_9(esk9_0))&((~m1_subset_1(X44,u1_struct_0(esk9_0))|v5_pre_topc(k4_waybel_1(esk9_0,X44),esk9_0,esk9_0))&((((~v2_struct_0(esk10_0)&v4_orders_2(esk10_0))&v7_waybel_0(esk10_0))&l1_waybel_0(esk10_0,esk9_0))&(v10_waybel_0(esk10_0,esk9_0)&(~r1_waybel_9(esk9_0,esk10_0)|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).
% 0.88/1.06  fof(c_0_14, plain, ![X19]:((l1_pre_topc(X19)|~l1_waybel_9(X19))&(l1_orders_2(X19)|~l1_waybel_9(X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).
% 0.88/1.06  cnf(c_0_15, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.88/1.06  cnf(c_0_16, negated_conjecture, (v1_lattice3(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.06  cnf(c_0_17, plain, (l1_orders_2(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.88/1.06  cnf(c_0_18, negated_conjecture, (l1_waybel_9(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.06  fof(c_0_19, plain, ![X31, X32]:((m1_subset_1(esk5_2(X31,X32),u1_struct_0(X31))|(v2_struct_0(X32)|~v4_orders_2(X32)|~v7_waybel_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~v8_pre_topc(X31)|~v1_compts_1(X31)|~l1_pre_topc(X31)))&(r3_waybel_9(X31,X32,esk5_2(X31,X32))|(v2_struct_0(X32)|~v4_orders_2(X32)|~v7_waybel_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~v8_pre_topc(X31)|~v1_compts_1(X31)|~l1_pre_topc(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_waybel_9])])])])])])).
% 0.88/1.06  cnf(c_0_20, negated_conjecture, (~l1_orders_2(esk9_0)|~v2_struct_0(esk9_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.88/1.06  cnf(c_0_21, negated_conjecture, (l1_orders_2(esk9_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.88/1.06  cnf(c_0_22, plain, (m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.88/1.06  cnf(c_0_23, negated_conjecture, (l1_waybel_0(esk10_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.06  cnf(c_0_24, negated_conjecture, (v7_waybel_0(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.06  cnf(c_0_25, negated_conjecture, (v1_compts_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.06  cnf(c_0_26, negated_conjecture, (v4_orders_2(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.06  cnf(c_0_27, negated_conjecture, (v8_pre_topc(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.06  cnf(c_0_28, negated_conjecture, (v2_pre_topc(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.06  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.06  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21])])).
% 0.88/1.06  fof(c_0_31, plain, ![X39, X40, X41]:((m1_subset_1(esk8_3(X39,X40,X41),u1_struct_0(X39))|~v10_waybel_0(X41,X39)|~r3_waybel_9(X39,X41,X40)|X40=k1_waybel_2(X39,X41)|(v2_struct_0(X41)|~v4_orders_2(X41)|~v7_waybel_0(X41)|~l1_waybel_0(X41,X39))|~m1_subset_1(X40,u1_struct_0(X39))|(~v2_pre_topc(X39)|~v8_pre_topc(X39)|~v3_orders_2(X39)|~v4_orders_2(X39)|~v5_orders_2(X39)|~v1_lattice3(X39)|~v2_lattice3(X39)|~v1_compts_1(X39)|~l1_waybel_9(X39)))&(~v5_pre_topc(k4_waybel_1(X39,esk8_3(X39,X40,X41)),X39,X39)|~v10_waybel_0(X41,X39)|~r3_waybel_9(X39,X41,X40)|X40=k1_waybel_2(X39,X41)|(v2_struct_0(X41)|~v4_orders_2(X41)|~v7_waybel_0(X41)|~l1_waybel_0(X41,X39))|~m1_subset_1(X40,u1_struct_0(X39))|(~v2_pre_topc(X39)|~v8_pre_topc(X39)|~v3_orders_2(X39)|~v4_orders_2(X39)|~v5_orders_2(X39)|~v1_lattice3(X39)|~v2_lattice3(X39)|~v1_compts_1(X39)|~l1_waybel_9(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_waybel_9])])])])])])).
% 0.88/1.06  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk5_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~l1_pre_topc(esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])]), c_0_29]), c_0_30])).
% 0.88/1.06  cnf(c_0_33, plain, (l1_pre_topc(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.88/1.06  cnf(c_0_34, plain, (r3_waybel_9(X1,X2,esk5_2(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.88/1.06  fof(c_0_35, plain, ![X20, X21, X22, X23]:((m1_subset_1(esk3_4(X20,X21,X22,X23),u1_struct_0(X20))|X22!=X23|~v10_waybel_0(X21,X20)|~r3_waybel_9(X20,X21,X22)|r2_lattice3(X20,k2_relset_1(u1_struct_0(X21),u1_struct_0(X20),u1_waybel_0(X20,X21)),X23)|~m1_subset_1(X23,u1_struct_0(X20))|~m1_subset_1(X22,u1_struct_0(X20))|(v2_struct_0(X21)|~v4_orders_2(X21)|~v7_waybel_0(X21)|~l1_waybel_0(X21,X20))|(~v2_pre_topc(X20)|~v8_pre_topc(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~v1_lattice3(X20)|~v2_lattice3(X20)|~v1_compts_1(X20)|~l1_waybel_9(X20)))&(~v5_pre_topc(k4_waybel_1(X20,esk3_4(X20,X21,X22,X23)),X20,X20)|X22!=X23|~v10_waybel_0(X21,X20)|~r3_waybel_9(X20,X21,X22)|r2_lattice3(X20,k2_relset_1(u1_struct_0(X21),u1_struct_0(X20),u1_waybel_0(X20,X21)),X23)|~m1_subset_1(X23,u1_struct_0(X20))|~m1_subset_1(X22,u1_struct_0(X20))|(v2_struct_0(X21)|~v4_orders_2(X21)|~v7_waybel_0(X21)|~l1_waybel_0(X21,X20))|(~v2_pre_topc(X20)|~v8_pre_topc(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~v1_lattice3(X20)|~v2_lattice3(X20)|~v1_compts_1(X20)|~l1_waybel_9(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l48_waybel_9])])])])])])).
% 0.88/1.06  cnf(c_0_36, plain, (m1_subset_1(esk8_3(X1,X2,X3),u1_struct_0(X1))|X2=k1_waybel_2(X1,X3)|v2_struct_0(X3)|~v10_waybel_0(X3,X1)|~r3_waybel_9(X1,X3,X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.88/1.06  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk5_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_18])])).
% 0.88/1.06  cnf(c_0_38, negated_conjecture, (v2_lattice3(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.06  cnf(c_0_39, negated_conjecture, (v4_orders_2(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.06  cnf(c_0_40, negated_conjecture, (v5_orders_2(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.06  cnf(c_0_41, negated_conjecture, (v3_orders_2(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.06  cnf(c_0_42, negated_conjecture, (r3_waybel_9(esk9_0,esk10_0,esk5_2(esk9_0,esk10_0))|~l1_pre_topc(esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])]), c_0_29]), c_0_30])).
% 0.88/1.06  cnf(c_0_43, plain, (X2=k1_waybel_2(X1,X3)|v2_struct_0(X3)|~v5_pre_topc(k4_waybel_1(X1,esk8_3(X1,X2,X3)),X1,X1)|~v10_waybel_0(X3,X1)|~r3_waybel_9(X1,X3,X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.88/1.06  cnf(c_0_44, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X1))|r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)|v2_struct_0(X2)|X3!=X4|~v10_waybel_0(X2,X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.88/1.06  fof(c_0_45, plain, ![X10, X11, X13, X14, X15]:((((m1_subset_1(esk1_2(X10,X11),u1_struct_0(X10))|~r1_yellow_0(X10,X11)|(~v5_orders_2(X10)|~l1_orders_2(X10)))&(r2_lattice3(X10,X11,esk1_2(X10,X11))|~r1_yellow_0(X10,X11)|(~v5_orders_2(X10)|~l1_orders_2(X10))))&(~m1_subset_1(X13,u1_struct_0(X10))|(~r2_lattice3(X10,X11,X13)|r1_orders_2(X10,esk1_2(X10,X11),X13))|~r1_yellow_0(X10,X11)|(~v5_orders_2(X10)|~l1_orders_2(X10))))&((m1_subset_1(esk2_3(X10,X14,X15),u1_struct_0(X10))|(~m1_subset_1(X15,u1_struct_0(X10))|~r2_lattice3(X10,X14,X15))|r1_yellow_0(X10,X14)|(~v5_orders_2(X10)|~l1_orders_2(X10)))&((r2_lattice3(X10,X14,esk2_3(X10,X14,X15))|(~m1_subset_1(X15,u1_struct_0(X10))|~r2_lattice3(X10,X14,X15))|r1_yellow_0(X10,X14)|(~v5_orders_2(X10)|~l1_orders_2(X10)))&(~r1_orders_2(X10,X15,esk2_3(X10,X14,X15))|(~m1_subset_1(X15,u1_struct_0(X10))|~r2_lattice3(X10,X14,X15))|r1_yellow_0(X10,X14)|(~v5_orders_2(X10)|~l1_orders_2(X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_yellow_0])])])])])])).
% 0.88/1.06  cnf(c_0_46, negated_conjecture, (esk5_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,X1)|m1_subset_1(esk8_3(esk9_0,esk5_2(esk9_0,esk10_0),X1),u1_struct_0(esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~v10_waybel_0(X1,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_47, negated_conjecture, (v10_waybel_0(esk10_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.06  cnf(c_0_48, negated_conjecture, (r3_waybel_9(esk9_0,esk10_0,esk5_2(esk9_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_33]), c_0_18])])).
% 0.88/1.06  cnf(c_0_49, negated_conjecture, (esk5_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~v10_waybel_0(X1,esk9_0)|~v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk5_2(esk9_0,esk10_0),X1)),esk9_0,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_37]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_50, plain, (r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)|m1_subset_1(esk3_4(X1,X2,X3,X3),u1_struct_0(X1))|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~v10_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X2)|~v4_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X2,X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_44])).
% 0.88/1.06  cnf(c_0_51, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.88/1.06  cnf(c_0_52, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,X1),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.06  cnf(c_0_53, negated_conjecture, (esk5_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk5_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_24]), c_0_26]), c_0_23])]), c_0_29])).
% 0.88/1.06  cnf(c_0_54, negated_conjecture, (esk5_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|~v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk5_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_47]), c_0_48]), c_0_24]), c_0_26]), c_0_23])]), c_0_29])).
% 0.88/1.06  cnf(c_0_55, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X1)),esk5_2(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,X1,esk5_2(esk9_0,esk10_0),esk5_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~v10_waybel_0(X1,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_37]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  fof(c_0_56, plain, ![X34, X35, X38]:((m1_subset_1(esk6_2(X34,X35),u1_struct_0(X34))|(~m1_subset_1(X38,u1_struct_0(X34))|(~r3_waybel_9(X34,X35,X38)|r2_hidden(X38,k10_yellow_6(X34,X35))))|(v2_struct_0(X35)|~v4_orders_2(X35)|~v7_waybel_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~v8_pre_topc(X34)|~v1_compts_1(X34)|~l1_pre_topc(X34)))&((m1_subset_1(esk7_2(X34,X35),u1_struct_0(X34))|(~m1_subset_1(X38,u1_struct_0(X34))|(~r3_waybel_9(X34,X35,X38)|r2_hidden(X38,k10_yellow_6(X34,X35))))|(v2_struct_0(X35)|~v4_orders_2(X35)|~v7_waybel_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~v8_pre_topc(X34)|~v1_compts_1(X34)|~l1_pre_topc(X34)))&(((r3_waybel_9(X34,X35,esk6_2(X34,X35))|(~m1_subset_1(X38,u1_struct_0(X34))|(~r3_waybel_9(X34,X35,X38)|r2_hidden(X38,k10_yellow_6(X34,X35))))|(v2_struct_0(X35)|~v4_orders_2(X35)|~v7_waybel_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~v8_pre_topc(X34)|~v1_compts_1(X34)|~l1_pre_topc(X34)))&(r3_waybel_9(X34,X35,esk7_2(X34,X35))|(~m1_subset_1(X38,u1_struct_0(X34))|(~r3_waybel_9(X34,X35,X38)|r2_hidden(X38,k10_yellow_6(X34,X35))))|(v2_struct_0(X35)|~v4_orders_2(X35)|~v7_waybel_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~v8_pre_topc(X34)|~v1_compts_1(X34)|~l1_pre_topc(X34))))&(esk6_2(X34,X35)!=esk7_2(X34,X35)|(~m1_subset_1(X38,u1_struct_0(X34))|(~r3_waybel_9(X34,X35,X38)|r2_hidden(X38,k10_yellow_6(X34,X35))))|(v2_struct_0(X35)|~v4_orders_2(X35)|~v7_waybel_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~v8_pre_topc(X34)|~v1_compts_1(X34)|~l1_pre_topc(X34)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t33_waybel_9])])])])])])).
% 0.88/1.06  cnf(c_0_57, negated_conjecture, (r1_yellow_0(esk9_0,X1)|m1_subset_1(esk2_3(esk9_0,X1,esk5_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r2_lattice3(esk9_0,X1,esk5_2(esk9_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_37]), c_0_40]), c_0_21])])).
% 0.88/1.06  cnf(c_0_58, negated_conjecture, (esk5_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.88/1.06  cnf(c_0_59, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk5_2(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,esk5_2(esk9_0,esk10_0),esk5_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_47]), c_0_48]), c_0_24]), c_0_26]), c_0_23])]), c_0_29])).
% 0.88/1.06  cnf(c_0_60, plain, (m1_subset_1(esk7_2(X1,X2),u1_struct_0(X1))|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.88/1.06  cnf(c_0_61, plain, (r2_lattice3(X1,X2,esk2_3(X1,X2,X3))|r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.88/1.06  fof(c_0_62, plain, ![X17, X18]:((~r1_waybel_9(X17,X18)|r1_yellow_0(X17,k2_relset_1(u1_struct_0(X18),u1_struct_0(X17),u1_waybel_0(X17,X18)))|~l1_waybel_0(X18,X17)|~l1_orders_2(X17))&(~r1_yellow_0(X17,k2_relset_1(u1_struct_0(X18),u1_struct_0(X17),u1_waybel_0(X17,X18)))|r1_waybel_9(X17,X18)|~l1_waybel_0(X18,X17)|~l1_orders_2(X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_waybel_9])])])])).
% 0.88/1.06  cnf(c_0_63, negated_conjecture, (r1_yellow_0(esk9_0,X1)|m1_subset_1(esk2_3(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r2_lattice3(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58]), c_0_58])).
% 0.88/1.06  cnf(c_0_64, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_58]), c_0_58]), c_0_58])).
% 0.88/1.06  cnf(c_0_65, negated_conjecture, (r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))|m1_subset_1(esk7_2(esk9_0,X1),u1_struct_0(esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_pre_topc(esk9_0)|~l1_waybel_0(X1,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_37]), c_0_25]), c_0_27]), c_0_28])]), c_0_30])).
% 0.88/1.06  cnf(c_0_66, negated_conjecture, (r2_lattice3(esk9_0,X1,esk2_3(esk9_0,X1,esk5_2(esk9_0,esk10_0)))|r1_yellow_0(esk9_0,X1)|~r2_lattice3(esk9_0,X1,esk5_2(esk9_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_37]), c_0_40]), c_0_21])])).
% 0.88/1.06  cnf(c_0_67, plain, (r1_waybel_9(X1,X2)|~r1_yellow_0(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))|~l1_waybel_0(X2,X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.88/1.06  cnf(c_0_68, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.88/1.06  cnf(c_0_69, negated_conjecture, (r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))|m1_subset_1(esk7_2(esk9_0,X1),u1_struct_0(esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_33]), c_0_18])])).
% 0.88/1.06  cnf(c_0_70, negated_conjecture, (r2_lattice3(esk9_0,X1,esk2_3(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0)))|r1_yellow_0(esk9_0,X1)|~r2_lattice3(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_58]), c_0_58])).
% 0.88/1.06  cnf(c_0_71, plain, (m1_subset_1(esk6_2(X1,X2),u1_struct_0(X1))|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.88/1.06  fof(c_0_72, plain, ![X25, X26, X27, X28, X30]:((m1_subset_1(esk4_4(X25,X26,X27,X28),u1_struct_0(X25))|X27!=X28|~r3_waybel_9(X25,X26,X27)|(~m1_subset_1(X30,u1_struct_0(X25))|(~r2_lattice3(X25,k2_relset_1(u1_struct_0(X26),u1_struct_0(X25),u1_waybel_0(X25,X26)),X30)|r3_orders_2(X25,X28,X30)))|~m1_subset_1(X28,u1_struct_0(X25))|~m1_subset_1(X27,u1_struct_0(X25))|(v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25))|(~v2_pre_topc(X25)|~v8_pre_topc(X25)|~v3_orders_2(X25)|~v4_orders_2(X25)|~v5_orders_2(X25)|~v1_lattice3(X25)|~v2_lattice3(X25)|~v1_compts_1(X25)|~l1_waybel_9(X25)))&(~v5_pre_topc(k4_waybel_1(X25,esk4_4(X25,X26,X27,X28)),X25,X25)|X27!=X28|~r3_waybel_9(X25,X26,X27)|(~m1_subset_1(X30,u1_struct_0(X25))|(~r2_lattice3(X25,k2_relset_1(u1_struct_0(X26),u1_struct_0(X25),u1_waybel_0(X25,X26)),X30)|r3_orders_2(X25,X28,X30)))|~m1_subset_1(X28,u1_struct_0(X25))|~m1_subset_1(X27,u1_struct_0(X25))|(v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25))|(~v2_pre_topc(X25)|~v8_pre_topc(X25)|~v3_orders_2(X25)|~v4_orders_2(X25)|~v5_orders_2(X25)|~v1_lattice3(X25)|~v2_lattice3(X25)|~v1_compts_1(X25)|~l1_waybel_9(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l49_waybel_9])])])])])])).
% 0.88/1.06  cnf(c_0_73, negated_conjecture, (~r1_waybel_9(esk9_0,esk10_0)|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.06  cnf(c_0_74, negated_conjecture, (r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_75, negated_conjecture, (r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_23]), c_0_48]), c_0_24]), c_0_26])]), c_0_29])).
% 0.88/1.06  cnf(c_0_76, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_70, c_0_64])).
% 0.88/1.06  cnf(c_0_77, negated_conjecture, (r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))|m1_subset_1(esk6_2(esk9_0,X1),u1_struct_0(esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_pre_topc(esk9_0)|~l1_waybel_0(X1,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_37]), c_0_25]), c_0_27]), c_0_28])]), c_0_30])).
% 0.88/1.06  cnf(c_0_78, plain, (m1_subset_1(esk4_4(X1,X2,X3,X4),u1_struct_0(X1))|r3_orders_2(X1,X4,X5)|v2_struct_0(X2)|X3!=X4|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X5,u1_struct_0(X1))|~r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.88/1.06  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.88/1.06  cnf(c_0_80, negated_conjecture, (r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(rw,[status(thm)],[c_0_75, c_0_58])).
% 0.88/1.06  cnf(c_0_81, negated_conjecture, (r1_waybel_9(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_76]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_82, negated_conjecture, (r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))|m1_subset_1(esk6_2(esk9_0,X1),u1_struct_0(esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_33]), c_0_18])])).
% 0.88/1.06  fof(c_0_83, plain, ![X6, X7, X8]:((~r3_orders_2(X6,X7,X8)|r1_orders_2(X6,X7,X8)|(v2_struct_0(X6)|~v3_orders_2(X6)|~l1_orders_2(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))&(~r1_orders_2(X6,X7,X8)|r3_orders_2(X6,X7,X8)|(v2_struct_0(X6)|~v3_orders_2(X6)|~l1_orders_2(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.88/1.06  cnf(c_0_84, plain, (r3_orders_2(X1,X2,X3)|m1_subset_1(esk4_4(X1,X4,X2,X2),u1_struct_0(X1))|v2_struct_0(X4)|~r3_waybel_9(X1,X4,X2)|~v7_waybel_0(X4)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X4)|~v4_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X4,X1)|~r2_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_78])).
% 0.88/1.06  cnf(c_0_85, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.88/1.06  cnf(c_0_86, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_81])).
% 0.88/1.06  cnf(c_0_87, negated_conjecture, (r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_23]), c_0_48]), c_0_24]), c_0_26])]), c_0_29])).
% 0.88/1.06  cnf(c_0_88, plain, (r1_yellow_0(X1,X3)|~r1_orders_2(X1,X2,esk2_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.88/1.06  cnf(c_0_89, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.88/1.06  cnf(c_0_90, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_91, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_86, c_0_80])).
% 0.88/1.06  cnf(c_0_92, negated_conjecture, (r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(rw,[status(thm)],[c_0_87, c_0_58])).
% 0.88/1.06  cnf(c_0_93, negated_conjecture, (r1_yellow_0(esk9_0,X1)|~r2_lattice3(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~r1_orders_2(esk9_0,esk5_2(esk9_0,esk10_0),esk2_3(esk9_0,X1,esk5_2(esk9_0,esk10_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_37]), c_0_40]), c_0_21])])).
% 0.88/1.06  cnf(c_0_94, negated_conjecture, (r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_85]), c_0_21]), c_0_41])]), c_0_30])).
% 0.88/1.06  cnf(c_0_95, negated_conjecture, (m1_subset_1(k1_waybel_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(rw,[status(thm)],[c_0_37, c_0_58])).
% 0.88/1.06  cnf(c_0_96, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_23]), c_0_24]), c_0_26])]), c_0_29]), c_0_91])).
% 0.88/1.06  cnf(c_0_97, negated_conjecture, (r3_waybel_9(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0))), inference(rw,[status(thm)],[c_0_48, c_0_58])).
% 0.88/1.06  cnf(c_0_98, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_79, c_0_92])).
% 0.88/1.06  cnf(c_0_99, negated_conjecture, (r1_yellow_0(esk9_0,X1)|~r2_lattice3(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0))|~r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_58]), c_0_58]), c_0_58])).
% 0.88/1.06  cnf(c_0_100, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.88/1.06  cnf(c_0_101, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_102, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_98]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_103, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_86, c_0_92])).
% 0.88/1.06  cnf(c_0_104, plain, (r3_orders_2(X1,X4,X5)|v2_struct_0(X2)|~v5_pre_topc(k4_waybel_1(X1,esk4_4(X1,X2,X3,X4)),X1,X1)|X3!=X4|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X5,u1_struct_0(X1))|~r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.88/1.06  cnf(c_0_105, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_64])).
% 0.88/1.06  cnf(c_0_106, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.88/1.06  cnf(c_0_107, negated_conjecture, (r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_98]), c_0_21]), c_0_41])]), c_0_30])).
% 0.88/1.06  cnf(c_0_108, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_23]), c_0_24]), c_0_26])]), c_0_29]), c_0_103])).
% 0.88/1.06  cnf(c_0_109, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X4)|~r3_waybel_9(X1,X4,X2)|~v5_pre_topc(k4_waybel_1(X1,esk4_4(X1,X4,X2,X2)),X1,X1)|~v7_waybel_0(X4)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X4)|~v4_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X4,X1)|~r2_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_104])).
% 0.88/1.06  cnf(c_0_110, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.88/1.06  cnf(c_0_111, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_107, c_0_95])).
% 0.88/1.06  cnf(c_0_112, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_113, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_85]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_114, negated_conjecture, (r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_110]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_115, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 0.88/1.06  cnf(c_0_116, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_23]), c_0_24]), c_0_26])]), c_0_29]), c_0_91])).
% 0.88/1.06  cnf(c_0_117, negated_conjecture, (m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_114]), c_0_80])).
% 0.88/1.06  cnf(c_0_118, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_105, c_0_115])).
% 0.88/1.06  cnf(c_0_119, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_120, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_117])).
% 0.88/1.06  cnf(c_0_121, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_98]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_122, negated_conjecture, (r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_118]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_123, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_119, c_0_120])).
% 0.88/1.06  cnf(c_0_124, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_23]), c_0_24]), c_0_26])]), c_0_29]), c_0_103])).
% 0.88/1.06  cnf(c_0_125, negated_conjecture, (m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_122]), c_0_92])).
% 0.88/1.06  cnf(c_0_126, plain, (r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)|v2_struct_0(X2)|~v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X2,X3,X4)),X1,X1)|X3!=X4|~v10_waybel_0(X2,X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.88/1.06  cnf(c_0_127, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_100, c_0_123])).
% 0.88/1.06  cnf(c_0_128, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_129, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_125])).
% 0.88/1.06  cnf(c_0_130, plain, (r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~v10_waybel_0(X2,X1)|~v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X2,X3,X3)),X1,X1)|~v7_waybel_0(X2)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X2)|~v4_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X2,X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_126])).
% 0.88/1.06  cnf(c_0_131, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_105, c_0_127])).
% 0.88/1.06  cnf(c_0_132, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_128, c_0_129])).
% 0.88/1.06  cnf(c_0_133, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X1)),esk5_2(esk9_0,esk10_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~v10_waybel_0(X1,esk9_0)|~v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,X1,esk5_2(esk9_0,esk10_0),esk5_2(esk9_0,esk10_0))),esk9_0,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_37]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_134, negated_conjecture, (r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_131]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_135, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_111, c_0_132])).
% 0.88/1.06  cnf(c_0_136, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X1)),k1_waybel_2(esk9_0,esk10_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0))|~v10_waybel_0(X1,esk9_0)|~v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133, c_0_58]), c_0_58]), c_0_58]), c_0_58])).
% 0.88/1.06  cnf(c_0_137, negated_conjecture, (m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_134]), c_0_80])).
% 0.88/1.06  cnf(c_0_138, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_105, c_0_135])).
% 0.88/1.06  cnf(c_0_139, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_47]), c_0_97]), c_0_24]), c_0_26]), c_0_23])]), c_0_29])).
% 0.88/1.06  cnf(c_0_140, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_137])).
% 0.88/1.06  cnf(c_0_141, negated_conjecture, (r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_138]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_142, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_139, c_0_140])).
% 0.88/1.06  cnf(c_0_143, negated_conjecture, (m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_141]), c_0_92])).
% 0.88/1.06  cnf(c_0_144, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_63, c_0_142])).
% 0.88/1.06  cnf(c_0_145, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_143])).
% 0.88/1.06  cnf(c_0_146, negated_conjecture, (r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_144]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_147, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_70, c_0_142])).
% 0.88/1.06  cnf(c_0_148, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_139, c_0_145])).
% 0.88/1.06  cnf(c_0_149, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_146]), c_0_80])).
% 0.88/1.06  cnf(c_0_150, negated_conjecture, (r1_waybel_9(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_147]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_151, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_63, c_0_148])).
% 0.88/1.06  cnf(c_0_152, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_149]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_153, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_150]), c_0_80])).
% 0.88/1.06  cnf(c_0_154, negated_conjecture, (r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_151]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_155, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_70, c_0_148])).
% 0.88/1.06  cnf(c_0_156, negated_conjecture, (r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_149]), c_0_21]), c_0_41])]), c_0_30])).
% 0.88/1.06  cnf(c_0_157, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_23]), c_0_24]), c_0_26])]), c_0_29]), c_0_153])).
% 0.88/1.06  cnf(c_0_158, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_154]), c_0_92])).
% 0.88/1.06  cnf(c_0_159, negated_conjecture, (r1_waybel_9(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_155]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_160, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_156, c_0_95])).
% 0.88/1.06  cnf(c_0_161, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_162, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_158]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_163, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_159]), c_0_92])).
% 0.88/1.06  cnf(c_0_164, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_142])).
% 0.88/1.06  cnf(c_0_165, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_160, c_0_161])).
% 0.88/1.06  cnf(c_0_166, negated_conjecture, (r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_158]), c_0_21]), c_0_41])]), c_0_30])).
% 0.88/1.06  cnf(c_0_167, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_23]), c_0_24]), c_0_26])]), c_0_29]), c_0_163])).
% 0.88/1.06  cnf(c_0_168, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_164, c_0_165])).
% 0.88/1.06  cnf(c_0_169, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_166, c_0_95])).
% 0.88/1.06  cnf(c_0_170, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_171, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_149]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_172, negated_conjecture, (r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_168]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_173, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_148])).
% 0.88/1.06  cnf(c_0_174, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_169, c_0_170])).
% 0.88/1.06  cnf(c_0_175, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_23]), c_0_24]), c_0_26])]), c_0_29]), c_0_153])).
% 0.88/1.06  cnf(c_0_176, negated_conjecture, (m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_172]), c_0_80])).
% 0.88/1.06  cnf(c_0_177, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_173, c_0_174])).
% 0.88/1.06  cnf(c_0_178, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_179, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_176])).
% 0.88/1.06  cnf(c_0_180, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_158]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_181, negated_conjecture, (r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_177]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_182, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_178, c_0_179])).
% 0.88/1.06  cnf(c_0_183, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180, c_0_23]), c_0_24]), c_0_26])]), c_0_29]), c_0_163])).
% 0.88/1.06  cnf(c_0_184, negated_conjecture, (m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_181]), c_0_92])).
% 0.88/1.06  cnf(c_0_185, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_160, c_0_182])).
% 0.88/1.06  cnf(c_0_186, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_187, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_184])).
% 0.88/1.06  cnf(c_0_188, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_164, c_0_185])).
% 0.88/1.06  cnf(c_0_189, plain, (r3_waybel_9(X1,X2,esk7_2(X1,X2))|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.88/1.06  cnf(c_0_190, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_186, c_0_187])).
% 0.88/1.06  cnf(c_0_191, negated_conjecture, (r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_188]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_192, negated_conjecture, (r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))|r3_waybel_9(esk9_0,X1,esk7_2(esk9_0,X1))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_pre_topc(esk9_0)|~l1_waybel_0(X1,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189, c_0_95]), c_0_25]), c_0_27]), c_0_28])]), c_0_30])).
% 0.88/1.06  cnf(c_0_193, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_169, c_0_190])).
% 0.88/1.06  cnf(c_0_194, negated_conjecture, (m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_191]), c_0_80])).
% 0.88/1.06  cnf(c_0_195, negated_conjecture, (r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))|r3_waybel_9(esk9_0,X1,esk7_2(esk9_0,X1))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192, c_0_33]), c_0_18])])).
% 0.88/1.06  cnf(c_0_196, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_173, c_0_193])).
% 0.88/1.06  cnf(c_0_197, plain, (r3_waybel_9(X1,X2,esk6_2(X1,X2))|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.88/1.06  cnf(c_0_198, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,X1)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),X1),u1_struct_0(esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk7_2(esk9_0,esk10_0))|~v10_waybel_0(X1,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_194]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_199, negated_conjecture, (r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_195, c_0_23]), c_0_97]), c_0_24]), c_0_26])]), c_0_29])).
% 0.88/1.06  cnf(c_0_200, negated_conjecture, (r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_196]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_201, negated_conjecture, (r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))|r3_waybel_9(esk9_0,X1,esk6_2(esk9_0,X1))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_pre_topc(esk9_0)|~l1_waybel_0(X1,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197, c_0_95]), c_0_25]), c_0_27]), c_0_28])]), c_0_30])).
% 0.88/1.06  cnf(c_0_202, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_47]), c_0_24]), c_0_26]), c_0_23])]), c_0_29])).
% 0.88/1.06  cnf(c_0_203, negated_conjecture, (r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_79, c_0_199])).
% 0.88/1.06  cnf(c_0_204, negated_conjecture, (m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_200]), c_0_92])).
% 0.88/1.06  cnf(c_0_205, negated_conjecture, (r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))|r3_waybel_9(esk9_0,X1,esk6_2(esk9_0,X1))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,k1_waybel_2(esk9_0,esk10_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201, c_0_33]), c_0_18])])).
% 0.88/1.06  cnf(c_0_206, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_202, c_0_203])).
% 0.88/1.06  cnf(c_0_207, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,X1)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),X1),u1_struct_0(esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk6_2(esk9_0,esk10_0))|~v10_waybel_0(X1,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_204]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_208, negated_conjecture, (r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205, c_0_23]), c_0_97]), c_0_24]), c_0_26])]), c_0_29])).
% 0.88/1.06  cnf(c_0_209, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_206]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_210, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_207, c_0_47]), c_0_24]), c_0_26]), c_0_23])]), c_0_29])).
% 0.88/1.06  cnf(c_0_211, negated_conjecture, (r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_79, c_0_208])).
% 0.88/1.06  cnf(c_0_212, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_209, c_0_23]), c_0_24]), c_0_26])]), c_0_29])).
% 0.88/1.06  cnf(c_0_213, negated_conjecture, (r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_86, c_0_199])).
% 0.88/1.06  cnf(c_0_214, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_210, c_0_211])).
% 0.88/1.06  cnf(c_0_215, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_206]), c_0_21]), c_0_41])]), c_0_30])).
% 0.88/1.06  cnf(c_0_216, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_212, c_0_213]), c_0_202])).
% 0.88/1.06  cnf(c_0_217, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_214]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_218, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_215, c_0_95])).
% 0.88/1.06  cnf(c_0_219, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_216, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_220, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_217, c_0_23]), c_0_24]), c_0_26])]), c_0_29])).
% 0.88/1.06  cnf(c_0_221, negated_conjecture, (r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_86, c_0_208])).
% 0.88/1.06  cnf(c_0_222, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_218, c_0_219])).
% 0.88/1.06  cnf(c_0_223, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_214]), c_0_21]), c_0_41])]), c_0_30])).
% 0.88/1.06  cnf(c_0_224, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_220, c_0_221]), c_0_210])).
% 0.88/1.06  cnf(c_0_225, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_105, c_0_222])).
% 0.88/1.06  cnf(c_0_226, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_223, c_0_95])).
% 0.88/1.06  cnf(c_0_227, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_224, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_228, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_206]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_229, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_225]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_230, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_226, c_0_227])).
% 0.88/1.06  cnf(c_0_231, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_228, c_0_23]), c_0_24]), c_0_26])]), c_0_29])).
% 0.88/1.06  cnf(c_0_232, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_229])).
% 0.88/1.06  cnf(c_0_233, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_105, c_0_230])).
% 0.88/1.06  cnf(c_0_234, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_231, c_0_213]), c_0_202])).
% 0.88/1.06  cnf(c_0_235, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_232, c_0_199]), c_0_202])).
% 0.88/1.06  cnf(c_0_236, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_214]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_237, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_233]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_238, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_234, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_239, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_235])).
% 0.88/1.06  cnf(c_0_240, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_236, c_0_23]), c_0_24]), c_0_26])]), c_0_29])).
% 0.88/1.06  cnf(c_0_241, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_237])).
% 0.88/1.06  cnf(c_0_242, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_238, c_0_239])).
% 0.88/1.06  cnf(c_0_243, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_240, c_0_221]), c_0_210])).
% 0.88/1.06  cnf(c_0_244, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_241, c_0_208]), c_0_210])).
% 0.88/1.06  cnf(c_0_245, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_218, c_0_242])).
% 0.88/1.06  cnf(c_0_246, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_247, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_244])).
% 0.88/1.06  cnf(c_0_248, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_105, c_0_245])).
% 0.88/1.06  cnf(c_0_249, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_246, c_0_247])).
% 0.88/1.06  cnf(c_0_250, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_248]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_251, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_226, c_0_249])).
% 0.88/1.06  cnf(c_0_252, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_250])).
% 0.88/1.06  cnf(c_0_253, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_105, c_0_251])).
% 0.88/1.06  cnf(c_0_254, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_252, c_0_199]), c_0_202])).
% 0.88/1.06  cnf(c_0_255, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_253]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_256, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_254])).
% 0.88/1.06  cnf(c_0_257, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_255])).
% 0.88/1.06  cnf(c_0_258, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_139, c_0_256])).
% 0.88/1.06  cnf(c_0_259, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_257, c_0_208]), c_0_210])).
% 0.88/1.06  cnf(c_0_260, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_63, c_0_258])).
% 0.88/1.06  cnf(c_0_261, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_259])).
% 0.88/1.06  cnf(c_0_262, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_260]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_263, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_70, c_0_258])).
% 0.88/1.06  cnf(c_0_264, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_139, c_0_261])).
% 0.88/1.06  cnf(c_0_265, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_262])).
% 0.88/1.06  cnf(c_0_266, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_waybel_9(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_263]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_267, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_63, c_0_264])).
% 0.88/1.06  cnf(c_0_268, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_265, c_0_199]), c_0_202])).
% 0.88/1.06  cnf(c_0_269, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_266])).
% 0.88/1.06  cnf(c_0_270, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_267]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_271, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_70, c_0_264])).
% 0.88/1.06  cnf(c_0_272, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_268]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_273, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_269, c_0_199]), c_0_202])).
% 0.88/1.06  cnf(c_0_274, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_270])).
% 0.88/1.06  cnf(c_0_275, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_waybel_9(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_271]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_276, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_268]), c_0_21]), c_0_41])]), c_0_30])).
% 0.88/1.06  cnf(c_0_277, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_272, c_0_23]), c_0_24]), c_0_26])]), c_0_29]), c_0_273])).
% 0.88/1.06  cnf(c_0_278, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_274, c_0_208]), c_0_210])).
% 0.88/1.06  cnf(c_0_279, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_275])).
% 0.88/1.06  cnf(c_0_280, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_276, c_0_95])).
% 0.88/1.06  cnf(c_0_281, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_277, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_282, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_278]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_283, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_279, c_0_208]), c_0_210])).
% 0.88/1.06  cnf(c_0_284, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_258])).
% 0.88/1.06  cnf(c_0_285, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_280, c_0_281])).
% 0.88/1.06  cnf(c_0_286, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_278]), c_0_21]), c_0_41])]), c_0_30])).
% 0.88/1.06  cnf(c_0_287, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_282, c_0_23]), c_0_24]), c_0_26])]), c_0_29]), c_0_283])).
% 0.88/1.06  cnf(c_0_288, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_284, c_0_285])).
% 0.88/1.06  cnf(c_0_289, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_286, c_0_95])).
% 0.88/1.06  cnf(c_0_290, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_287, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_291, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_288]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_292, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_264])).
% 0.88/1.06  cnf(c_0_293, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_289, c_0_290])).
% 0.88/1.06  cnf(c_0_294, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_268]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_295, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_291])).
% 0.88/1.06  cnf(c_0_296, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_292, c_0_293])).
% 0.88/1.06  cnf(c_0_297, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_294, c_0_23]), c_0_24]), c_0_26])]), c_0_29]), c_0_273])).
% 0.88/1.06  cnf(c_0_298, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_295, c_0_199]), c_0_202])).
% 0.88/1.06  cnf(c_0_299, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_296]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_300, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_297, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_301, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_298])).
% 0.88/1.06  cnf(c_0_302, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_278]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_303, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_299])).
% 0.88/1.06  cnf(c_0_304, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_300, c_0_301])).
% 0.88/1.06  cnf(c_0_305, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_302, c_0_23]), c_0_24]), c_0_26])]), c_0_29]), c_0_283])).
% 0.88/1.06  cnf(c_0_306, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_303, c_0_208]), c_0_210])).
% 0.88/1.06  cnf(c_0_307, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_280, c_0_304])).
% 0.88/1.06  cnf(c_0_308, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_305, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_309, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_306])).
% 0.88/1.06  cnf(c_0_310, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_284, c_0_307])).
% 0.88/1.06  cnf(c_0_311, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_308, c_0_309])).
% 0.88/1.06  cnf(c_0_312, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_310]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_313, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_289, c_0_311])).
% 0.88/1.06  cnf(c_0_314, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk7_2(esk9_0,esk10_0))|~v10_waybel_0(X1,esk9_0)|~v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),X1)),esk9_0,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_194]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_315, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_312])).
% 0.88/1.06  cnf(c_0_316, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_292, c_0_313])).
% 0.88/1.06  cnf(c_0_317, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|~r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_314, c_0_47]), c_0_24]), c_0_26]), c_0_23])]), c_0_29])).
% 0.88/1.06  cnf(c_0_318, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_315, c_0_199]), c_0_202])).
% 0.88/1.06  cnf(c_0_319, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_316]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_320, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_317, c_0_203])).
% 0.88/1.06  cnf(c_0_321, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_52, c_0_318])).
% 0.88/1.06  cnf(c_0_322, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk6_2(esk9_0,esk10_0))|~v10_waybel_0(X1,esk9_0)|~v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),X1)),esk9_0,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_204]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_323, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_319])).
% 0.88/1.06  cnf(c_0_324, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_320, c_0_321])).
% 0.88/1.06  cnf(c_0_325, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|~r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_322, c_0_47]), c_0_24]), c_0_26]), c_0_23])]), c_0_29])).
% 0.88/1.06  cnf(c_0_326, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_323, c_0_208]), c_0_210])).
% 0.88/1.06  cnf(c_0_327, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_324]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_328, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_325, c_0_211])).
% 0.88/1.06  cnf(c_0_329, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_52, c_0_326])).
% 0.88/1.06  cnf(c_0_330, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_327, c_0_23]), c_0_24]), c_0_26])]), c_0_29])).
% 0.88/1.06  cnf(c_0_331, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_328, c_0_329])).
% 0.88/1.06  cnf(c_0_332, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_324]), c_0_21]), c_0_41])]), c_0_30])).
% 0.88/1.06  cnf(c_0_333, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_330, c_0_213])).
% 0.88/1.06  cnf(c_0_334, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_331]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_335, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_332, c_0_95])).
% 0.88/1.06  cnf(c_0_336, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_333, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_337, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_334, c_0_23]), c_0_24]), c_0_26])]), c_0_29])).
% 0.88/1.06  cnf(c_0_338, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_335, c_0_336])).
% 0.88/1.06  cnf(c_0_339, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_331]), c_0_21]), c_0_41])]), c_0_30])).
% 0.88/1.06  cnf(c_0_340, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_337, c_0_221])).
% 0.88/1.06  cnf(c_0_341, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_105, c_0_338])).
% 0.88/1.06  cnf(c_0_342, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_339, c_0_95])).
% 0.88/1.06  cnf(c_0_343, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_340, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_344, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_324]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_345, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_341]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_346, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_342, c_0_343])).
% 0.88/1.06  cnf(c_0_347, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_344, c_0_23]), c_0_24]), c_0_26])]), c_0_29])).
% 0.88/1.06  cnf(c_0_348, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_345]), c_0_199])).
% 0.88/1.06  cnf(c_0_349, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_105, c_0_346])).
% 0.88/1.06  cnf(c_0_350, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_347, c_0_213])).
% 0.88/1.06  cnf(c_0_351, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_317, c_0_348]), c_0_321])).
% 0.88/1.06  cnf(c_0_352, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_331]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_353, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_349]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_354, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_350, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_355, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_351])).
% 0.88/1.06  cnf(c_0_356, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_352, c_0_23]), c_0_24]), c_0_26])]), c_0_29])).
% 0.88/1.06  cnf(c_0_357, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_353]), c_0_208])).
% 0.88/1.06  cnf(c_0_358, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_354, c_0_355])).
% 0.88/1.06  cnf(c_0_359, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_356, c_0_221])).
% 0.88/1.06  cnf(c_0_360, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_325, c_0_357]), c_0_329])).
% 0.88/1.06  cnf(c_0_361, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_335, c_0_358])).
% 0.88/1.06  cnf(c_0_362, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_359, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_363, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_360])).
% 0.88/1.06  cnf(c_0_364, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_105, c_0_361])).
% 0.88/1.06  cnf(c_0_365, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_362, c_0_363])).
% 0.88/1.06  cnf(c_0_366, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_364]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_367, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_342, c_0_365])).
% 0.88/1.06  cnf(c_0_368, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_366]), c_0_199])).
% 0.88/1.06  cnf(c_0_369, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_105, c_0_367])).
% 0.88/1.06  cnf(c_0_370, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_317, c_0_368]), c_0_321])).
% 0.88/1.06  cnf(c_0_371, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_369]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_372, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_52, c_0_370])).
% 0.88/1.06  cnf(c_0_373, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_371]), c_0_208])).
% 0.88/1.06  cnf(c_0_374, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_139, c_0_372])).
% 0.88/1.06  cnf(c_0_375, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_325, c_0_373]), c_0_329])).
% 0.88/1.06  cnf(c_0_376, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_63, c_0_374])).
% 0.88/1.06  cnf(c_0_377, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_52, c_0_375])).
% 0.88/1.06  cnf(c_0_378, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_376]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_379, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_139, c_0_377])).
% 0.88/1.06  cnf(c_0_380, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_378])).
% 0.88/1.06  cnf(c_0_381, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_63, c_0_379])).
% 0.88/1.06  cnf(c_0_382, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_380, c_0_199])).
% 0.88/1.06  cnf(c_0_383, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_70, c_0_374])).
% 0.88/1.06  cnf(c_0_384, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_381]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_385, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_317, c_0_382]), c_0_321])).
% 0.88/1.06  cnf(c_0_386, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_waybel_9(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_383]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_387, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_384])).
% 0.88/1.06  cnf(c_0_388, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_385]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_389, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_386])).
% 0.88/1.06  cnf(c_0_390, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_387, c_0_208])).
% 0.88/1.06  cnf(c_0_391, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_70, c_0_379])).
% 0.88/1.06  cnf(c_0_392, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_388, c_0_23]), c_0_24]), c_0_26])]), c_0_29])).
% 0.88/1.06  cnf(c_0_393, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_389, c_0_199])).
% 0.88/1.06  cnf(c_0_394, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_325, c_0_390]), c_0_329])).
% 0.88/1.06  cnf(c_0_395, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_waybel_9(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_391]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_396, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_385]), c_0_21]), c_0_41])]), c_0_30])).
% 0.88/1.06  cnf(c_0_397, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_392, c_0_393])).
% 0.88/1.06  cnf(c_0_398, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_394]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_399, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_395])).
% 0.88/1.06  cnf(c_0_400, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_396, c_0_95])).
% 0.88/1.06  cnf(c_0_401, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_397, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_402, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_398, c_0_23]), c_0_24]), c_0_26])]), c_0_29])).
% 0.88/1.06  cnf(c_0_403, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_399, c_0_208])).
% 0.88/1.06  cnf(c_0_404, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|~r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_374])).
% 0.88/1.06  cnf(c_0_405, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_400, c_0_401])).
% 0.88/1.06  cnf(c_0_406, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_394]), c_0_21]), c_0_41])]), c_0_30])).
% 0.88/1.06  cnf(c_0_407, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_402, c_0_403])).
% 0.88/1.06  cnf(c_0_408, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_404, c_0_405])).
% 0.88/1.06  cnf(c_0_409, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_406, c_0_95])).
% 0.88/1.06  cnf(c_0_410, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_407, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_411, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_385]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_412, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_408]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_413, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|~r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_379])).
% 0.88/1.06  cnf(c_0_414, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_409, c_0_410])).
% 0.88/1.06  cnf(c_0_415, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_411, c_0_23]), c_0_24]), c_0_26])]), c_0_29])).
% 0.88/1.06  cnf(c_0_416, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_412]), c_0_199])).
% 0.88/1.06  cnf(c_0_417, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_413, c_0_414])).
% 0.88/1.06  cnf(c_0_418, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_415, c_0_393])).
% 0.88/1.06  cnf(c_0_419, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_317, c_0_416]), c_0_321])).
% 0.88/1.06  cnf(c_0_420, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_394]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_421, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_417]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_422, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_418, c_0_95]), c_0_97])])).
% 0.88/1.06  cnf(c_0_423, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_52, c_0_419])).
% 0.88/1.06  cnf(c_0_424, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_420, c_0_23]), c_0_24]), c_0_26])]), c_0_29])).
% 0.88/1.06  cnf(c_0_425, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_421]), c_0_208])).
% 0.88/1.06  cnf(c_0_426, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_422, c_0_423])).
% 0.88/1.06  cnf(c_0_427, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_424, c_0_403])).
% 0.88/1.06  cnf(c_0_428, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_325, c_0_425]), c_0_329])).
% 0.88/1.06  cnf(c_0_429, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_400, c_0_426])).
% 0.88/1.06  cnf(c_0_430, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_427, c_0_95]), c_0_97])])).
% 0.88/1.06  cnf(c_0_431, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_52, c_0_428])).
% 0.88/1.06  cnf(c_0_432, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_404, c_0_429])).
% 0.88/1.06  cnf(c_0_433, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_430, c_0_431])).
% 0.88/1.06  cnf(c_0_434, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_waybel_9(esk9_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_432]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_435, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_409, c_0_433])).
% 0.88/1.06  cnf(c_0_436, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_434]), c_0_199])).
% 0.88/1.06  cnf(c_0_437, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_413, c_0_435])).
% 0.88/1.06  cnf(c_0_438, plain, (r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|esk6_2(X1,X2)!=esk7_2(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.88/1.06  cnf(c_0_439, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_317, c_0_436]), c_0_321])).
% 0.88/1.06  cnf(c_0_440, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_waybel_9(esk9_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_437]), c_0_23]), c_0_21])])).
% 0.88/1.06  cnf(c_0_441, negated_conjecture, (r2_hidden(X1,k10_yellow_6(esk9_0,esk10_0))|esk6_2(esk9_0,esk10_0)!=k1_waybel_2(esk9_0,esk10_0)|~r3_waybel_9(esk9_0,esk10_0,X1)|~l1_pre_topc(esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_438, c_0_439]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_23])]), c_0_29]), c_0_30])).
% 0.88/1.06  cnf(c_0_442, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_440]), c_0_208])).
% 0.88/1.06  cnf(c_0_443, negated_conjecture, (r2_hidden(X1,k10_yellow_6(esk9_0,esk10_0))|esk6_2(esk9_0,esk10_0)!=k1_waybel_2(esk9_0,esk10_0)|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_441, c_0_33]), c_0_18])])).
% 0.88/1.06  cnf(c_0_444, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_2(esk9_0,esk10_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_325, c_0_442]), c_0_329])).
% 0.88/1.06  cnf(c_0_445, negated_conjecture, (r2_hidden(X1,k10_yellow_6(esk9_0,esk10_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_443, c_0_444])])).
% 0.88/1.06  cnf(c_0_446, negated_conjecture, (r2_hidden(k1_waybel_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_445, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_447, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_446])])).
% 0.88/1.06  cnf(c_0_448, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_447]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_449, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_446])])).
% 0.88/1.06  cnf(c_0_450, negated_conjecture, (r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_447]), c_0_21]), c_0_41])]), c_0_30])).
% 0.88/1.06  cnf(c_0_451, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_448, c_0_23]), c_0_24]), c_0_26])]), c_0_29]), c_0_449])).
% 0.88/1.06  cnf(c_0_452, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_450, c_0_95])).
% 0.88/1.06  cnf(c_0_453, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_451, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_454, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_452, c_0_453])).
% 0.88/1.06  cnf(c_0_455, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_447]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_456, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_105, c_0_454])).
% 0.88/1.06  cnf(c_0_457, negated_conjecture, (~r1_waybel_9(esk9_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_446])])).
% 0.88/1.06  cnf(c_0_458, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_455, c_0_23]), c_0_24]), c_0_26])]), c_0_29]), c_0_449])).
% 0.88/1.06  cnf(c_0_459, negated_conjecture, (m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_456]), c_0_23]), c_0_21])]), c_0_457])).
% 0.88/1.06  cnf(c_0_460, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_458, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_461, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_459])).
% 0.88/1.06  cnf(c_0_462, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_460, c_0_461])).
% 0.88/1.06  cnf(c_0_463, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_452, c_0_462])).
% 0.88/1.06  cnf(c_0_464, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_105, c_0_463])).
% 0.88/1.06  cnf(c_0_465, negated_conjecture, (m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_464]), c_0_23]), c_0_21])]), c_0_457])).
% 0.88/1.06  cnf(c_0_466, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_52, c_0_465])).
% 0.88/1.06  cnf(c_0_467, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_139, c_0_466])])).
% 0.88/1.06  cnf(c_0_468, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_63, c_0_467])).
% 0.88/1.06  cnf(c_0_469, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_468]), c_0_23]), c_0_21])]), c_0_457])).
% 0.88/1.06  cnf(c_0_470, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_70, c_0_467])).
% 0.88/1.06  cnf(c_0_471, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_469]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_472, negated_conjecture, (r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_470]), c_0_23]), c_0_21])]), c_0_457])).
% 0.88/1.06  cnf(c_0_473, negated_conjecture, (r1_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_469]), c_0_21]), c_0_41])]), c_0_30])).
% 0.88/1.06  cnf(c_0_474, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_471, c_0_23]), c_0_24]), c_0_26]), c_0_472])]), c_0_29])).
% 0.88/1.06  cnf(c_0_475, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_473, c_0_95])).
% 0.88/1.06  cnf(c_0_476, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_474, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_477, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|~r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_467])).
% 0.88/1.06  cnf(c_0_478, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_475, c_0_476])).
% 0.88/1.06  cnf(c_0_479, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r2_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_469]), c_0_25]), c_0_38]), c_0_39]), c_0_27]), c_0_28]), c_0_18]), c_0_40]), c_0_16]), c_0_41])])).
% 0.88/1.06  cnf(c_0_480, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_477, c_0_478])).
% 0.88/1.06  cnf(c_0_481, negated_conjecture, (r3_orders_2(esk9_0,X1,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_479, c_0_23]), c_0_24]), c_0_26]), c_0_472])]), c_0_29])).
% 0.88/1.06  cnf(c_0_482, negated_conjecture, (m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_480]), c_0_23]), c_0_21])]), c_0_457])).
% 0.88/1.06  cnf(c_0_483, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_481, c_0_97]), c_0_95])])).
% 0.88/1.06  cnf(c_0_484, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_2(esk9_0,esk10_0),k1_waybel_2(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_52, c_0_482])).
% 0.88/1.06  cnf(c_0_485, negated_conjecture, (r3_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_483, c_0_484])])).
% 0.88/1.06  cnf(c_0_486, negated_conjecture, (r1_orders_2(esk9_0,k1_waybel_2(esk9_0,esk10_0),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_2(esk9_0,esk10_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_475, c_0_485])])).
% 0.88/1.06  cnf(c_0_487, negated_conjecture, (r1_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_477, c_0_486])])).
% 0.88/1.06  cnf(c_0_488, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_487]), c_0_23]), c_0_21])]), c_0_457]), ['proof']).
% 0.88/1.06  # SZS output end CNFRefutation
% 0.88/1.06  # Proof object total steps             : 489
% 0.88/1.06  # Proof object clause steps            : 466
% 0.88/1.06  # Proof object formula steps           : 23
% 0.88/1.06  # Proof object conjectures             : 444
% 0.88/1.06  # Proof object clause conjectures      : 441
% 0.88/1.06  # Proof object formula conjectures     : 3
% 0.88/1.06  # Proof object initial clauses used    : 37
% 0.88/1.06  # Proof object initial formulas used   : 11
% 0.88/1.06  # Proof object generating inferences   : 407
% 0.88/1.06  # Proof object simplifying inferences  : 959
% 0.88/1.06  # Training examples: 0 positive, 0 negative
% 0.88/1.06  # Parsed axioms                        : 11
% 0.88/1.06  # Removed by relevancy pruning/SinE    : 0
% 0.88/1.06  # Initial clauses                      : 42
% 0.88/1.06  # Removed in clause preprocessing      : 0
% 0.88/1.06  # Initial clauses in saturation        : 42
% 0.88/1.06  # Processed clauses                    : 2890
% 0.88/1.06  # ...of these trivial                  : 1
% 0.88/1.06  # ...subsumed                          : 417
% 0.88/1.06  # ...remaining for further processing  : 2472
% 0.88/1.06  # Other redundant clauses eliminated   : 4
% 0.88/1.06  # Clauses deleted for lack of memory   : 0
% 0.88/1.06  # Backward-subsumed                    : 1377
% 0.88/1.06  # Backward-rewritten                   : 868
% 0.88/1.06  # Generated clauses                    : 6382
% 0.88/1.06  # ...of the previous two non-trivial   : 6337
% 0.88/1.06  # Contextual simplify-reflections      : 138
% 0.88/1.06  # Paramodulations                      : 6376
% 0.88/1.06  # Factorizations                       : 0
% 0.88/1.06  # Equation resolutions                 : 4
% 0.88/1.06  # Propositional unsat checks           : 0
% 0.88/1.06  #    Propositional check models        : 0
% 0.88/1.06  #    Propositional check unsatisfiable : 0
% 0.88/1.06  #    Propositional clauses             : 0
% 0.88/1.06  #    Propositional clauses after purity: 0
% 0.88/1.06  #    Propositional unsat core size     : 0
% 0.88/1.06  #    Propositional preprocessing time  : 0.000
% 0.88/1.06  #    Propositional encoding time       : 0.000
% 0.88/1.06  #    Propositional solver time         : 0.000
% 0.88/1.06  #    Success case prop preproc time    : 0.000
% 0.88/1.06  #    Success case prop encoding time   : 0.000
% 0.88/1.06  #    Success case prop solver time     : 0.000
% 0.88/1.06  # Current number of processed clauses  : 179
% 0.88/1.06  #    Positive orientable unit clauses  : 39
% 0.88/1.06  #    Positive unorientable unit clauses: 0
% 0.88/1.06  #    Negative unit clauses             : 3
% 0.88/1.06  #    Non-unit-clauses                  : 137
% 0.88/1.06  # Current number of unprocessed clauses: 74
% 0.88/1.06  # ...number of literals in the above   : 302
% 0.88/1.06  # Current number of archived formulas  : 0
% 0.88/1.06  # Current number of archived clauses   : 2289
% 0.88/1.06  # Clause-clause subsumption calls (NU) : 425630
% 0.88/1.06  # Rec. Clause-clause subsumption calls : 39664
% 0.88/1.06  # Non-unit clause-clause subsumptions  : 1931
% 0.88/1.06  # Unit Clause-clause subsumption calls : 1637
% 0.88/1.06  # Rewrite failures with RHS unbound    : 0
% 0.88/1.06  # BW rewrite match attempts            : 70
% 0.88/1.06  # BW rewrite match successes           : 23
% 0.88/1.06  # Condensation attempts                : 0
% 0.88/1.06  # Condensation successes               : 0
% 0.88/1.06  # Termbank termtop insertions          : 441217
% 0.88/1.06  
% 0.88/1.06  # -------------------------------------------------
% 0.88/1.06  # User time                : 0.707 s
% 0.88/1.06  # System time              : 0.005 s
% 0.88/1.06  # Total time               : 0.712 s
% 0.88/1.06  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
