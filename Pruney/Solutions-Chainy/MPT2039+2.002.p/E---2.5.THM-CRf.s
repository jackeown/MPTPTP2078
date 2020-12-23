%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:47 EST 2020

% Result     : Theorem 0.67s
% Output     : CNFRefutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  491 (162002832728 expanded)
%              Number of clauses        :  468 (50539687847 expanded)
%              Number of leaves         :   11 (40055256329 expanded)
%              Depth                    :  159
%              Number of atoms          : 2438 (1946877797498 expanded)
%              Number of equality atoms :  270 (5738992672 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_9)).

fof(dt_l1_waybel_9,axiom,(
    ! [X1] :
      ( l1_waybel_9(X1)
     => ( l1_pre_topc(X1)
        & l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_waybel_9)).

fof(t30_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) )
               => ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) ) )
              & ( ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) )
               => ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_waybel_9)).

fof(d3_waybel_9,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ( r1_waybel_9(X1,X2)
          <=> r1_yellow_0(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_waybel_9)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

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
    ! [X18] :
      ( ( l1_pre_topc(X18)
        | ~ l1_waybel_9(X18) )
      & ( l1_orders_2(X18)
        | ~ l1_waybel_9(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).

fof(c_0_13,negated_conjecture,(
    ! [X43] :
      ( v2_pre_topc(esk8_0)
      & v8_pre_topc(esk8_0)
      & v3_orders_2(esk8_0)
      & v4_orders_2(esk8_0)
      & v5_orders_2(esk8_0)
      & v1_lattice3(esk8_0)
      & v2_lattice3(esk8_0)
      & v1_compts_1(esk8_0)
      & l1_waybel_9(esk8_0)
      & ( ~ m1_subset_1(X43,u1_struct_0(esk8_0))
        | v5_pre_topc(k4_waybel_1(esk8_0,X43),esk8_0,esk8_0) )
      & ~ v2_struct_0(esk9_0)
      & v4_orders_2(esk9_0)
      & v7_waybel_0(esk9_0)
      & l1_waybel_0(esk9_0,esk8_0)
      & v10_waybel_0(esk9_0,esk8_0)
      & ( ~ r1_waybel_9(esk8_0,esk9_0)
        | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).

fof(c_0_14,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | ~ v1_lattice3(X9)
      | ~ v2_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

cnf(c_0_15,plain,
    ( l1_orders_2(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l1_waybel_9(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X30,X31] :
      ( ( m1_subset_1(esk4_2(X30,X31),u1_struct_0(X30))
        | v2_struct_0(X31)
        | ~ v4_orders_2(X31)
        | ~ v7_waybel_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ v8_pre_topc(X30)
        | ~ v1_compts_1(X30)
        | ~ l1_pre_topc(X30) )
      & ( r3_waybel_9(X30,X31,esk4_2(X30,X31))
        | v2_struct_0(X31)
        | ~ v4_orders_2(X31)
        | ~ v7_waybel_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ v8_pre_topc(X30)
        | ~ v1_compts_1(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_waybel_9])])])])])])).

cnf(c_0_18,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v1_lattice3(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk8_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( l1_waybel_0(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( v7_waybel_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( v1_compts_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( v4_orders_2(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( v8_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

fof(c_0_30,plain,(
    ! [X38,X39,X40] :
      ( ( m1_subset_1(esk7_3(X38,X39,X40),u1_struct_0(X38))
        | ~ v10_waybel_0(X40,X38)
        | ~ r3_waybel_9(X38,X40,X39)
        | X39 = k1_waybel_2(X38,X40)
        | v2_struct_0(X40)
        | ~ v4_orders_2(X40)
        | ~ v7_waybel_0(X40)
        | ~ l1_waybel_0(X40,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | ~ v2_pre_topc(X38)
        | ~ v8_pre_topc(X38)
        | ~ v3_orders_2(X38)
        | ~ v4_orders_2(X38)
        | ~ v5_orders_2(X38)
        | ~ v1_lattice3(X38)
        | ~ v2_lattice3(X38)
        | ~ v1_compts_1(X38)
        | ~ l1_waybel_9(X38) )
      & ( ~ v5_pre_topc(k4_waybel_1(X38,esk7_3(X38,X39,X40)),X38,X38)
        | ~ v10_waybel_0(X40,X38)
        | ~ r3_waybel_9(X38,X40,X39)
        | X39 = k1_waybel_2(X38,X40)
        | v2_struct_0(X40)
        | ~ v4_orders_2(X40)
        | ~ v7_waybel_0(X40)
        | ~ l1_waybel_0(X40,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | ~ v2_pre_topc(X38)
        | ~ v8_pre_topc(X38)
        | ~ v3_orders_2(X38)
        | ~ v4_orders_2(X38)
        | ~ v5_orders_2(X38)
        | ~ v1_lattice3(X38)
        | ~ v2_lattice3(X38)
        | ~ v1_compts_1(X38)
        | ~ l1_waybel_9(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_waybel_9])])])])])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ l1_pre_topc(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])]),c_0_28]),c_0_29])).

cnf(c_0_32,plain,
    ( l1_pre_topc(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,plain,
    ( r3_waybel_9(X1,X2,esk4_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_34,plain,(
    ! [X19,X20,X21,X22] :
      ( ( m1_subset_1(esk2_4(X19,X20,X21,X22),u1_struct_0(X19))
        | X21 != X22
        | ~ v10_waybel_0(X20,X19)
        | ~ r3_waybel_9(X19,X20,X21)
        | r2_lattice3(X19,k2_relset_1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20)),X22)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | v2_struct_0(X20)
        | ~ v4_orders_2(X20)
        | ~ v7_waybel_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | ~ v2_pre_topc(X19)
        | ~ v8_pre_topc(X19)
        | ~ v3_orders_2(X19)
        | ~ v4_orders_2(X19)
        | ~ v5_orders_2(X19)
        | ~ v1_lattice3(X19)
        | ~ v2_lattice3(X19)
        | ~ v1_compts_1(X19)
        | ~ l1_waybel_9(X19) )
      & ( ~ v5_pre_topc(k4_waybel_1(X19,esk2_4(X19,X20,X21,X22)),X19,X19)
        | X21 != X22
        | ~ v10_waybel_0(X20,X19)
        | ~ r3_waybel_9(X19,X20,X21)
        | r2_lattice3(X19,k2_relset_1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20)),X22)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | v2_struct_0(X20)
        | ~ v4_orders_2(X20)
        | ~ v7_waybel_0(X20)
        | ~ l1_waybel_0(X20,X19)
        | ~ v2_pre_topc(X19)
        | ~ v8_pre_topc(X19)
        | ~ v3_orders_2(X19)
        | ~ v4_orders_2(X19)
        | ~ v5_orders_2(X19)
        | ~ v1_lattice3(X19)
        | ~ v2_lattice3(X19)
        | ~ v1_compts_1(X19)
        | ~ l1_waybel_9(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l48_waybel_9])])])])])])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
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
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_16])])).

cnf(c_0_37,negated_conjecture,
    ( v2_lattice3(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( v4_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( v5_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( v3_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( r3_waybel_9(esk8_0,esk9_0,esk4_2(esk8_0,esk9_0))
    | ~ l1_pre_topc(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])]),c_0_28]),c_0_29])).

cnf(c_0_42,plain,
    ( X2 = k1_waybel_2(X1,X3)
    | v2_struct_0(X3)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk7_3(X1,X2,X3)),X1,X1)
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
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X1))
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
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_44,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( r2_lattice3(X10,X12,X11)
        | X11 != k1_yellow_0(X10,X12)
        | ~ r1_yellow_0(X10,X12)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_lattice3(X10,X12,X13)
        | r1_orders_2(X10,X11,X13)
        | X11 != k1_yellow_0(X10,X12)
        | ~ r1_yellow_0(X10,X12)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( X11 = k1_yellow_0(X10,X14)
        | m1_subset_1(esk1_3(X10,X11,X14),u1_struct_0(X10))
        | ~ r2_lattice3(X10,X14,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_yellow_0(X10,X14)
        | m1_subset_1(esk1_3(X10,X11,X14),u1_struct_0(X10))
        | ~ r2_lattice3(X10,X14,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( X11 = k1_yellow_0(X10,X14)
        | r2_lattice3(X10,X14,esk1_3(X10,X11,X14))
        | ~ r2_lattice3(X10,X14,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_yellow_0(X10,X14)
        | r2_lattice3(X10,X14,esk1_3(X10,X11,X14))
        | ~ r2_lattice3(X10,X14,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( X11 = k1_yellow_0(X10,X14)
        | ~ r1_orders_2(X10,X11,esk1_3(X10,X11,X14))
        | ~ r2_lattice3(X10,X14,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_yellow_0(X10,X14)
        | ~ r1_orders_2(X10,X11,esk1_3(X10,X11,X14))
        | ~ r2_lattice3(X10,X14,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

cnf(c_0_45,negated_conjecture,
    ( esk4_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,X1)
    | m1_subset_1(esk7_3(esk8_0,esk4_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))
    | ~ v10_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_46,negated_conjecture,
    ( v10_waybel_0(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_47,negated_conjecture,
    ( r3_waybel_9(esk8_0,esk9_0,esk4_2(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_32]),c_0_16])])).

cnf(c_0_48,negated_conjecture,
    ( esk4_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))
    | ~ v10_waybel_0(X1,esk8_0)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk4_2(esk8_0,esk9_0),X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_36]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_49,plain,
    ( r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)
    | m1_subset_1(esk2_4(X1,X2,X3,X3),u1_struct_0(X1))
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
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( r1_yellow_0(X1,X2)
    | m1_subset_1(esk1_3(X1,X3,X2),u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,X1),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,negated_conjecture,
    ( esk4_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk4_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_23]),c_0_25]),c_0_22])]),c_0_28])).

cnf(c_0_53,negated_conjecture,
    ( esk4_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk4_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_46]),c_0_47]),c_0_23]),c_0_25]),c_0_22])]),c_0_28])).

cnf(c_0_54,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X1)),esk4_2(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,X1,esk4_2(esk8_0,esk9_0),esk4_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))
    | ~ v10_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_36]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

fof(c_0_55,plain,(
    ! [X33,X34,X37] :
      ( ( m1_subset_1(esk5_2(X33,X34),u1_struct_0(X33))
        | ~ m1_subset_1(X37,u1_struct_0(X33))
        | ~ r3_waybel_9(X33,X34,X37)
        | r2_hidden(X37,k10_yellow_6(X33,X34))
        | v2_struct_0(X34)
        | ~ v4_orders_2(X34)
        | ~ v7_waybel_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ v8_pre_topc(X33)
        | ~ v1_compts_1(X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(esk6_2(X33,X34),u1_struct_0(X33))
        | ~ m1_subset_1(X37,u1_struct_0(X33))
        | ~ r3_waybel_9(X33,X34,X37)
        | r2_hidden(X37,k10_yellow_6(X33,X34))
        | v2_struct_0(X34)
        | ~ v4_orders_2(X34)
        | ~ v7_waybel_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ v8_pre_topc(X33)
        | ~ v1_compts_1(X33)
        | ~ l1_pre_topc(X33) )
      & ( r3_waybel_9(X33,X34,esk5_2(X33,X34))
        | ~ m1_subset_1(X37,u1_struct_0(X33))
        | ~ r3_waybel_9(X33,X34,X37)
        | r2_hidden(X37,k10_yellow_6(X33,X34))
        | v2_struct_0(X34)
        | ~ v4_orders_2(X34)
        | ~ v7_waybel_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ v8_pre_topc(X33)
        | ~ v1_compts_1(X33)
        | ~ l1_pre_topc(X33) )
      & ( r3_waybel_9(X33,X34,esk6_2(X33,X34))
        | ~ m1_subset_1(X37,u1_struct_0(X33))
        | ~ r3_waybel_9(X33,X34,X37)
        | r2_hidden(X37,k10_yellow_6(X33,X34))
        | v2_struct_0(X34)
        | ~ v4_orders_2(X34)
        | ~ v7_waybel_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ v8_pre_topc(X33)
        | ~ v1_compts_1(X33)
        | ~ l1_pre_topc(X33) )
      & ( esk5_2(X33,X34) != esk6_2(X33,X34)
        | ~ m1_subset_1(X37,u1_struct_0(X33))
        | ~ r3_waybel_9(X33,X34,X37)
        | r2_hidden(X37,k10_yellow_6(X33,X34))
        | v2_struct_0(X34)
        | ~ v4_orders_2(X34)
        | ~ v7_waybel_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ v8_pre_topc(X33)
        | ~ v1_compts_1(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t33_waybel_9])])])])])])).

cnf(c_0_56,negated_conjecture,
    ( r1_yellow_0(esk8_0,X1)
    | m1_subset_1(esk1_3(esk8_0,esk4_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))
    | ~ r2_lattice3(esk8_0,X1,esk4_2(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_36]),c_0_39]),c_0_20])])).

cnf(c_0_57,negated_conjecture,
    ( esk4_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk4_2(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,esk4_2(esk8_0,esk9_0),esk4_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_46]),c_0_47]),c_0_23]),c_0_25]),c_0_22])]),c_0_28])).

cnf(c_0_59,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,plain,
    ( r1_yellow_0(X1,X2)
    | r2_lattice3(X1,X2,esk1_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_61,plain,(
    ! [X16,X17] :
      ( ( ~ r1_waybel_9(X16,X17)
        | r1_yellow_0(X16,k2_relset_1(u1_struct_0(X17),u1_struct_0(X16),u1_waybel_0(X16,X17)))
        | ~ l1_waybel_0(X17,X16)
        | ~ l1_orders_2(X16) )
      & ( ~ r1_yellow_0(X16,k2_relset_1(u1_struct_0(X17),u1_struct_0(X16),u1_waybel_0(X16,X17)))
        | r1_waybel_9(X16,X17)
        | ~ l1_waybel_0(X17,X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_waybel_9])])])])).

cnf(c_0_62,negated_conjecture,
    ( r1_yellow_0(esk8_0,X1)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))
    | ~ r2_lattice3(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_57]),c_0_57]),c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))
    | m1_subset_1(esk6_2(esk8_0,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(esk8_0)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_36]),c_0_24]),c_0_26]),c_0_27])]),c_0_29])).

cnf(c_0_65,negated_conjecture,
    ( r2_lattice3(esk8_0,X1,esk1_3(esk8_0,esk4_2(esk8_0,esk9_0),X1))
    | r1_yellow_0(esk8_0,X1)
    | ~ r2_lattice3(esk8_0,X1,esk4_2(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_36]),c_0_39]),c_0_20])])).

cnf(c_0_66,plain,
    ( r1_waybel_9(X1,X2)
    | ~ r1_yellow_0(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))
    | m1_subset_1(esk6_2(esk8_0,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_32]),c_0_16])])).

cnf(c_0_69,negated_conjecture,
    ( r2_lattice3(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),X1))
    | r1_yellow_0(esk8_0,X1)
    | ~ r2_lattice3(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_57]),c_0_57])).

cnf(c_0_70,plain,
    ( m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))
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
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_71,plain,(
    ! [X24,X25,X26,X27,X29] :
      ( ( m1_subset_1(esk3_4(X24,X25,X26,X27),u1_struct_0(X24))
        | X26 != X27
        | ~ r3_waybel_9(X24,X25,X26)
        | ~ m1_subset_1(X29,u1_struct_0(X24))
        | ~ r2_lattice3(X24,k2_relset_1(u1_struct_0(X25),u1_struct_0(X24),u1_waybel_0(X24,X25)),X29)
        | r3_orders_2(X24,X27,X29)
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | v2_struct_0(X25)
        | ~ v4_orders_2(X25)
        | ~ v7_waybel_0(X25)
        | ~ l1_waybel_0(X25,X24)
        | ~ v2_pre_topc(X24)
        | ~ v8_pre_topc(X24)
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ v1_compts_1(X24)
        | ~ l1_waybel_9(X24) )
      & ( ~ v5_pre_topc(k4_waybel_1(X24,esk3_4(X24,X25,X26,X27)),X24,X24)
        | X26 != X27
        | ~ r3_waybel_9(X24,X25,X26)
        | ~ m1_subset_1(X29,u1_struct_0(X24))
        | ~ r2_lattice3(X24,k2_relset_1(u1_struct_0(X25),u1_struct_0(X24),u1_waybel_0(X24,X25)),X29)
        | r3_orders_2(X24,X27,X29)
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | v2_struct_0(X25)
        | ~ v4_orders_2(X25)
        | ~ v7_waybel_0(X25)
        | ~ l1_waybel_0(X25,X24)
        | ~ v2_pre_topc(X24)
        | ~ v8_pre_topc(X24)
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ v1_compts_1(X24)
        | ~ l1_waybel_9(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l49_waybel_9])])])])])])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_waybel_9(esk8_0,esk9_0)
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_73,negated_conjecture,
    ( r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_22]),c_0_20])])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_22]),c_0_47]),c_0_23]),c_0_25])]),c_0_28])).

cnf(c_0_75,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_63])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))
    | m1_subset_1(esk5_2(esk8_0,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(esk8_0)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_36]),c_0_24]),c_0_26]),c_0_27])]),c_0_29])).

cnf(c_0_77,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X1))
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
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_57])).

cnf(c_0_80,negated_conjecture,
    ( r1_waybel_9(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_75]),c_0_22]),c_0_20])])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))
    | m1_subset_1(esk5_2(esk8_0,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_32]),c_0_16])])).

fof(c_0_82,plain,(
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

cnf(c_0_83,plain,
    ( r3_orders_2(X1,X2,X3)
    | m1_subset_1(esk3_4(X1,X4,X2,X2),u1_struct_0(X1))
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
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_22]),c_0_47]),c_0_23]),c_0_25])]),c_0_28])).

cnf(c_0_87,plain,
    ( r1_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,X3,esk1_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_88,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_90,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_79])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_86,c_0_57])).

cnf(c_0_92,negated_conjecture,
    ( r1_yellow_0(esk8_0,X1)
    | ~ r2_lattice3(esk8_0,X1,esk4_2(esk8_0,esk9_0))
    | ~ r1_orders_2(esk8_0,esk4_2(esk8_0,esk9_0),esk1_3(esk8_0,esk4_2(esk8_0,esk9_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_36]),c_0_39]),c_0_20])])).

cnf(c_0_93,negated_conjecture,
    ( r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_84]),c_0_20]),c_0_40])]),c_0_29])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(k1_waybel_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_57])).

cnf(c_0_95,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( r3_waybel_9(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_57])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( r1_yellow_0(esk8_0,X1)
    | ~ r2_lattice3(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0))
    | ~ r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_57]),c_0_57]),c_0_57])).

cnf(c_0_99,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_100,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_94])])).

cnf(c_0_101,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_97]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_102,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_91])).

cnf(c_0_103,plain,
    ( r3_orders_2(X1,X4,X5)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X2,X3,X4)),X1,X1)
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
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_104,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_63])).

cnf(c_0_105,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_106,negated_conjecture,
    ( r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_97]),c_0_20]),c_0_40])]),c_0_29])).

cnf(c_0_107,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_102])).

cnf(c_0_108,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X4)
    | ~ r3_waybel_9(X1,X4,X2)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X4,X2,X2)),X1,X1)
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
    inference(er,[status(thm)],[c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_106,c_0_94])).

cnf(c_0_111,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_96]),c_0_94])])).

cnf(c_0_112,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_84]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_113,negated_conjecture,
    ( r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_109]),c_0_22]),c_0_20])])).

cnf(c_0_114,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_90])).

cnf(c_0_116,negated_conjecture,
    ( m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_113]),c_0_79])).

cnf(c_0_117,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_114])).

cnf(c_0_118,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_96]),c_0_94])])).

cnf(c_0_119,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_116])).

cnf(c_0_120,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_97]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_121,negated_conjecture,
    ( r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_117]),c_0_22]),c_0_20])])).

cnf(c_0_122,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_123,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_102])).

cnf(c_0_124,negated_conjecture,
    ( m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_121]),c_0_91])).

cnf(c_0_125,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_122])).

cnf(c_0_126,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_96]),c_0_94])])).

cnf(c_0_127,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_124])).

cnf(c_0_128,plain,
    ( r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk2_4(X1,X2,X3,X4)),X1,X1)
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
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_129,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_125])).

cnf(c_0_130,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_131,plain,
    ( r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ v10_waybel_0(X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk2_4(X1,X2,X3,X3)),X1,X1)
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
    inference(er,[status(thm)],[c_0_128])).

cnf(c_0_132,negated_conjecture,
    ( r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_129]),c_0_22]),c_0_20])])).

cnf(c_0_133,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_130])).

cnf(c_0_134,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X1)),k1_waybel_2(esk8_0,esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0))
    | ~ v10_waybel_0(X1,esk8_0)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_94]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_135,negated_conjecture,
    ( m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_132]),c_0_79])).

cnf(c_0_136,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_133])).

cnf(c_0_137,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_46]),c_0_96]),c_0_23]),c_0_25]),c_0_22])]),c_0_28])).

cnf(c_0_138,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_135])).

cnf(c_0_139,negated_conjecture,
    ( r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_136]),c_0_22]),c_0_20])])).

cnf(c_0_140,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_141,negated_conjecture,
    ( m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_139]),c_0_91])).

cnf(c_0_142,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_140])).

cnf(c_0_143,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_141])).

cnf(c_0_144,negated_conjecture,
    ( r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_142]),c_0_22]),c_0_20])])).

cnf(c_0_145,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_140])).

cnf(c_0_146,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_137,c_0_143])).

cnf(c_0_147,negated_conjecture,
    ( m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_144]),c_0_79])).

cnf(c_0_148,negated_conjecture,
    ( r1_waybel_9(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_145]),c_0_22]),c_0_20])])).

cnf(c_0_149,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_146])).

cnf(c_0_150,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_147]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_151,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_148]),c_0_79])).

cnf(c_0_152,negated_conjecture,
    ( r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_149]),c_0_22]),c_0_20])])).

cnf(c_0_153,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_146])).

cnf(c_0_154,negated_conjecture,
    ( r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_147]),c_0_20]),c_0_40])]),c_0_29])).

cnf(c_0_155,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_151])).

cnf(c_0_156,negated_conjecture,
    ( m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_152]),c_0_91])).

cnf(c_0_157,negated_conjecture,
    ( r1_waybel_9(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_153]),c_0_22]),c_0_20])])).

cnf(c_0_158,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_154,c_0_94])).

cnf(c_0_159,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_96]),c_0_94])])).

cnf(c_0_160,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_156]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_161,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_157]),c_0_91])).

cnf(c_0_162,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_140])).

cnf(c_0_163,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_158,c_0_159])).

cnf(c_0_164,negated_conjecture,
    ( r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_156]),c_0_20]),c_0_40])]),c_0_29])).

cnf(c_0_165,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_161])).

cnf(c_0_166,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_162,c_0_163])).

cnf(c_0_167,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_164,c_0_94])).

cnf(c_0_168,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_96]),c_0_94])])).

cnf(c_0_169,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_147]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_170,negated_conjecture,
    ( r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_166]),c_0_22]),c_0_20])])).

cnf(c_0_171,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_146])).

cnf(c_0_172,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_167,c_0_168])).

cnf(c_0_173,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_151])).

cnf(c_0_174,negated_conjecture,
    ( m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_170]),c_0_79])).

cnf(c_0_175,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_171,c_0_172])).

cnf(c_0_176,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_96]),c_0_94])])).

cnf(c_0_177,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_174])).

cnf(c_0_178,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_156]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_179,negated_conjecture,
    ( r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_175]),c_0_22]),c_0_20])])).

cnf(c_0_180,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_176,c_0_177])).

cnf(c_0_181,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_161])).

cnf(c_0_182,negated_conjecture,
    ( m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_179]),c_0_91])).

cnf(c_0_183,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_158,c_0_180])).

cnf(c_0_184,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_96]),c_0_94])])).

cnf(c_0_185,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_182])).

cnf(c_0_186,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_162,c_0_183])).

cnf(c_0_187,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_188,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_184,c_0_185])).

cnf(c_0_189,negated_conjecture,
    ( r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_186]),c_0_22]),c_0_20])])).

cnf(c_0_190,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))
    | r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,X1))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(esk8_0)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187,c_0_94]),c_0_24]),c_0_26]),c_0_27])]),c_0_29])).

cnf(c_0_191,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_167,c_0_188])).

cnf(c_0_192,negated_conjecture,
    ( m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_189]),c_0_79])).

cnf(c_0_193,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))
    | r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,X1))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190,c_0_32]),c_0_16])])).

cnf(c_0_194,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_171,c_0_191])).

cnf(c_0_195,plain,
    ( r3_waybel_9(X1,X2,esk5_2(X1,X2))
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
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_196,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,X1)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,esk9_0))
    | ~ v10_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_192]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_197,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))
    | r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193,c_0_22]),c_0_96]),c_0_23]),c_0_25])]),c_0_28])).

cnf(c_0_198,negated_conjecture,
    ( r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_194]),c_0_22]),c_0_20])])).

cnf(c_0_199,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))
    | r3_waybel_9(esk8_0,X1,esk5_2(esk8_0,X1))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(esk8_0)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_195,c_0_94]),c_0_24]),c_0_26]),c_0_27])]),c_0_29])).

cnf(c_0_200,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196,c_0_46]),c_0_23]),c_0_25]),c_0_22])]),c_0_28])).

cnf(c_0_201,negated_conjecture,
    ( r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_197])).

cnf(c_0_202,negated_conjecture,
    ( m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_198]),c_0_91])).

cnf(c_0_203,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))
    | r3_waybel_9(esk8_0,X1,esk5_2(esk8_0,X1))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199,c_0_32]),c_0_16])])).

cnf(c_0_204,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_200,c_0_201])).

cnf(c_0_205,negated_conjecture,
    ( r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_197])).

cnf(c_0_206,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,X1)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk5_2(esk8_0,esk9_0))
    | ~ v10_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_202]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_207,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))
    | r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203,c_0_22]),c_0_96]),c_0_23]),c_0_25])]),c_0_28])).

cnf(c_0_208,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_204]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_209,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_200,c_0_205])).

cnf(c_0_210,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_206,c_0_46]),c_0_23]),c_0_25]),c_0_22])]),c_0_28])).

cnf(c_0_211,negated_conjecture,
    ( r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_207])).

cnf(c_0_212,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_204]),c_0_20]),c_0_40])]),c_0_29])).

cnf(c_0_213,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_208,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_209])).

cnf(c_0_214,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_210,c_0_211])).

cnf(c_0_215,negated_conjecture,
    ( r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_207])).

cnf(c_0_216,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_212,c_0_94])).

cnf(c_0_217,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_213,c_0_96]),c_0_94])])).

cnf(c_0_218,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_214]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_219,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_210,c_0_215])).

cnf(c_0_220,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_216,c_0_217])).

cnf(c_0_221,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_214]),c_0_20]),c_0_40])]),c_0_29])).

cnf(c_0_222,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_218,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_219])).

cnf(c_0_223,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_220])).

cnf(c_0_224,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_221,c_0_94])).

cnf(c_0_225,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_222,c_0_96]),c_0_94])])).

cnf(c_0_226,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_223]),c_0_22]),c_0_20])])).

cnf(c_0_227,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_224,c_0_225])).

cnf(c_0_228,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_204]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_229,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_226])).

cnf(c_0_230,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_227])).

cnf(c_0_231,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_228,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_209])).

cnf(c_0_232,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_229,c_0_197]),c_0_200])).

cnf(c_0_233,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_230]),c_0_22]),c_0_20])])).

cnf(c_0_234,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_231,c_0_96]),c_0_94])])).

cnf(c_0_235,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_232])).

cnf(c_0_236,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_214]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_237,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_233])).

cnf(c_0_238,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_234,c_0_235])).

cnf(c_0_239,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_236,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_219])).

cnf(c_0_240,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_237,c_0_207]),c_0_210])).

cnf(c_0_241,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_216,c_0_238])).

cnf(c_0_242,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_239,c_0_96]),c_0_94])])).

cnf(c_0_243,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_240])).

cnf(c_0_244,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_241])).

cnf(c_0_245,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_242,c_0_243])).

cnf(c_0_246,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_244]),c_0_22]),c_0_20])])).

cnf(c_0_247,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_224,c_0_245])).

cnf(c_0_248,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_246])).

cnf(c_0_249,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_247])).

cnf(c_0_250,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_248,c_0_197]),c_0_200])).

cnf(c_0_251,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_249]),c_0_22]),c_0_20])])).

cnf(c_0_252,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_250])).

cnf(c_0_253,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_251])).

cnf(c_0_254,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_137,c_0_252])).

cnf(c_0_255,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_253,c_0_207]),c_0_210])).

cnf(c_0_256,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_254])).

cnf(c_0_257,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_255])).

cnf(c_0_258,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_256]),c_0_22]),c_0_20])])).

cnf(c_0_259,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_254])).

cnf(c_0_260,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_137,c_0_257])).

cnf(c_0_261,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_258])).

cnf(c_0_262,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_259]),c_0_22]),c_0_20])])).

cnf(c_0_263,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_260])).

cnf(c_0_264,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_261,c_0_197]),c_0_200])).

cnf(c_0_265,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_262])).

cnf(c_0_266,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_263]),c_0_22]),c_0_20])])).

cnf(c_0_267,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_260])).

cnf(c_0_268,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_264]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_269,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_265,c_0_197]),c_0_200])).

cnf(c_0_270,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_266])).

cnf(c_0_271,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_267]),c_0_22]),c_0_20])])).

cnf(c_0_272,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_264]),c_0_20]),c_0_40])]),c_0_29])).

cnf(c_0_273,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_268,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_269])).

cnf(c_0_274,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_270,c_0_207]),c_0_210])).

cnf(c_0_275,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_271])).

cnf(c_0_276,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_272,c_0_94])).

cnf(c_0_277,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_273,c_0_96]),c_0_94])])).

cnf(c_0_278,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_274]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_279,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_275,c_0_207]),c_0_210])).

cnf(c_0_280,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_254])).

cnf(c_0_281,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_276,c_0_277])).

cnf(c_0_282,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_274]),c_0_20]),c_0_40])]),c_0_29])).

cnf(c_0_283,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_278,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_279])).

cnf(c_0_284,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_280,c_0_281])).

cnf(c_0_285,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_282,c_0_94])).

cnf(c_0_286,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_283,c_0_96]),c_0_94])])).

cnf(c_0_287,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_284]),c_0_22]),c_0_20])])).

cnf(c_0_288,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_260])).

cnf(c_0_289,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_285,c_0_286])).

cnf(c_0_290,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_264]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_291,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_287])).

cnf(c_0_292,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_288,c_0_289])).

cnf(c_0_293,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_290,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_269])).

cnf(c_0_294,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_291,c_0_197]),c_0_200])).

cnf(c_0_295,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_292]),c_0_22]),c_0_20])])).

cnf(c_0_296,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_293,c_0_96]),c_0_94])])).

cnf(c_0_297,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_294])).

cnf(c_0_298,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_274]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_299,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_295])).

cnf(c_0_300,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_296,c_0_297])).

cnf(c_0_301,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_298,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_279])).

cnf(c_0_302,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_299,c_0_207]),c_0_210])).

cnf(c_0_303,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_276,c_0_300])).

cnf(c_0_304,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_301,c_0_96]),c_0_94])])).

cnf(c_0_305,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_302])).

cnf(c_0_306,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_280,c_0_303])).

cnf(c_0_307,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_304,c_0_305])).

cnf(c_0_308,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_306]),c_0_22]),c_0_20])])).

cnf(c_0_309,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_285,c_0_307])).

cnf(c_0_310,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,esk9_0))
    | ~ v10_waybel_0(X1,esk8_0)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_192]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_311,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_308])).

cnf(c_0_312,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_288,c_0_309])).

cnf(c_0_313,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | ~ r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_310,c_0_46]),c_0_23]),c_0_25]),c_0_22])]),c_0_28])).

cnf(c_0_314,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_311,c_0_197]),c_0_200])).

cnf(c_0_315,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_312]),c_0_22]),c_0_20])])).

cnf(c_0_316,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_313,c_0_201])).

cnf(c_0_317,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_314])).

cnf(c_0_318,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk5_2(esk8_0,esk9_0))
    | ~ v10_waybel_0(X1,esk8_0)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_202]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_319,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_315])).

cnf(c_0_320,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_316,c_0_317])).

cnf(c_0_321,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_313,c_0_205])).

cnf(c_0_322,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | ~ r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_318,c_0_46]),c_0_23]),c_0_25]),c_0_22])]),c_0_28])).

cnf(c_0_323,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_319,c_0_207]),c_0_210])).

cnf(c_0_324,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_320]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_325,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_321,c_0_317])).

cnf(c_0_326,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_322,c_0_211])).

cnf(c_0_327,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_323])).

cnf(c_0_328,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_320]),c_0_20]),c_0_40])]),c_0_29])).

cnf(c_0_329,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_324,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_325])).

cnf(c_0_330,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_326,c_0_327])).

cnf(c_0_331,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_322,c_0_215])).

cnf(c_0_332,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_328,c_0_94])).

cnf(c_0_333,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_329,c_0_96]),c_0_94])])).

cnf(c_0_334,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_330]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_335,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_331,c_0_327])).

cnf(c_0_336,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_332,c_0_333])).

cnf(c_0_337,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_330]),c_0_20]),c_0_40])]),c_0_29])).

cnf(c_0_338,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_334,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_335])).

cnf(c_0_339,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_336])).

cnf(c_0_340,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_337,c_0_94])).

cnf(c_0_341,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_338,c_0_96]),c_0_94])])).

cnf(c_0_342,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_339]),c_0_22]),c_0_20])])).

cnf(c_0_343,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_340,c_0_341])).

cnf(c_0_344,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_342])).

cnf(c_0_345,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_343])).

cnf(c_0_346,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_320]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_347,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_344,c_0_197])).

cnf(c_0_348,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_345]),c_0_22]),c_0_20])])).

cnf(c_0_349,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_346,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_325])).

cnf(c_0_350,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_313,c_0_347]),c_0_317])).

cnf(c_0_351,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_348])).

cnf(c_0_352,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_349,c_0_96]),c_0_94])])).

cnf(c_0_353,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_350])).

cnf(c_0_354,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_330]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_355,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_351,c_0_207])).

cnf(c_0_356,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_352,c_0_353])).

cnf(c_0_357,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_354,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_335])).

cnf(c_0_358,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_322,c_0_355]),c_0_327])).

cnf(c_0_359,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_332,c_0_356])).

cnf(c_0_360,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_357,c_0_96]),c_0_94])])).

cnf(c_0_361,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_358])).

cnf(c_0_362,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_359])).

cnf(c_0_363,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_360,c_0_361])).

cnf(c_0_364,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_362]),c_0_22]),c_0_20])])).

cnf(c_0_365,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_340,c_0_363])).

cnf(c_0_366,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_364])).

cnf(c_0_367,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_365])).

cnf(c_0_368,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_366,c_0_197])).

cnf(c_0_369,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_367]),c_0_22]),c_0_20])])).

cnf(c_0_370,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_313,c_0_368]),c_0_317])).

cnf(c_0_371,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_369])).

cnf(c_0_372,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_370])).

cnf(c_0_373,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_371,c_0_207])).

cnf(c_0_374,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_137,c_0_372])).

cnf(c_0_375,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_322,c_0_373]),c_0_327])).

cnf(c_0_376,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_374])).

cnf(c_0_377,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_375])).

cnf(c_0_378,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_376]),c_0_22]),c_0_20])])).

cnf(c_0_379,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_374])).

cnf(c_0_380,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_137,c_0_377])).

cnf(c_0_381,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_378])).

cnf(c_0_382,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_379]),c_0_22]),c_0_20])])).

cnf(c_0_383,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_380])).

cnf(c_0_384,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_381,c_0_197])).

cnf(c_0_385,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_382])).

cnf(c_0_386,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_383]),c_0_22]),c_0_20])])).

cnf(c_0_387,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_380])).

cnf(c_0_388,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_313,c_0_384]),c_0_317])).

cnf(c_0_389,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_385,c_0_197])).

cnf(c_0_390,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_386])).

cnf(c_0_391,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_387]),c_0_22]),c_0_20])])).

cnf(c_0_392,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_388]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_393,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_313,c_0_389]),c_0_317])).

cnf(c_0_394,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_390,c_0_207])).

cnf(c_0_395,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_391])).

cnf(c_0_396,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_388]),c_0_20]),c_0_40])]),c_0_29])).

cnf(c_0_397,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_392,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_393])).

cnf(c_0_398,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_322,c_0_394]),c_0_327])).

cnf(c_0_399,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_395,c_0_207])).

cnf(c_0_400,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_396,c_0_94])).

cnf(c_0_401,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_397,c_0_96]),c_0_94])])).

cnf(c_0_402,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_398]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_403,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_322,c_0_399]),c_0_327])).

cnf(c_0_404,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | ~ r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_374])).

cnf(c_0_405,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_400,c_0_401])).

cnf(c_0_406,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_398]),c_0_20]),c_0_40])]),c_0_29])).

cnf(c_0_407,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_402,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_403])).

cnf(c_0_408,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_404,c_0_405])).

cnf(c_0_409,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_406,c_0_94])).

cnf(c_0_410,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_407,c_0_96]),c_0_94])])).

cnf(c_0_411,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_408]),c_0_22]),c_0_20])])).

cnf(c_0_412,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | ~ r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_380])).

cnf(c_0_413,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_409,c_0_410])).

cnf(c_0_414,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_411])).

cnf(c_0_415,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_412,c_0_413])).

cnf(c_0_416,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_388]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_417,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_414,c_0_197])).

cnf(c_0_418,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_415]),c_0_22]),c_0_20])])).

cnf(c_0_419,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_416,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_393])).

cnf(c_0_420,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_313,c_0_417]),c_0_317])).

cnf(c_0_421,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_418])).

cnf(c_0_422,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_419,c_0_96]),c_0_94])])).

cnf(c_0_423,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_420])).

cnf(c_0_424,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_398]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_425,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_421,c_0_207])).

cnf(c_0_426,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_422,c_0_423])).

cnf(c_0_427,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_424,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_403])).

cnf(c_0_428,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_322,c_0_425]),c_0_327])).

cnf(c_0_429,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_400,c_0_426])).

cnf(c_0_430,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_427,c_0_96]),c_0_94])])).

cnf(c_0_431,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_428])).

cnf(c_0_432,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_404,c_0_429])).

cnf(c_0_433,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_430,c_0_431])).

cnf(c_0_434,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_432]),c_0_22]),c_0_20])])).

cnf(c_0_435,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_409,c_0_433])).

cnf(c_0_436,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_434])).

cnf(c_0_437,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_412,c_0_435])).

cnf(c_0_438,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_436,c_0_197])).

cnf(c_0_439,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r1_waybel_9(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_437]),c_0_22]),c_0_20])])).

cnf(c_0_440,plain,
    ( r2_hidden(X3,k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | esk5_2(X1,X2) != esk6_2(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_441,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_313,c_0_438]),c_0_317])).

cnf(c_0_442,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | ~ r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_439])).

cnf(c_0_443,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk8_0,esk9_0))
    | esk5_2(esk8_0,esk9_0) != k1_waybel_2(esk8_0,esk9_0)
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ l1_pre_topc(esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_440,c_0_441]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_22])]),c_0_28]),c_0_29])).

cnf(c_0_444,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_442,c_0_207])).

cnf(c_0_445,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk8_0,esk9_0))
    | esk5_2(esk8_0,esk9_0) != k1_waybel_2(esk8_0,esk9_0)
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_443,c_0_32]),c_0_16])])).

cnf(c_0_446,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_2(esk8_0,esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_322,c_0_444]),c_0_327])).

cnf(c_0_447,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk8_0,esk9_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_445,c_0_446])])).

cnf(c_0_448,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_447,c_0_96]),c_0_94])])).

cnf(c_0_449,negated_conjecture,
    ( m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_448])])).

cnf(c_0_450,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_449]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_451,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_448])])).

cnf(c_0_452,negated_conjecture,
    ( r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_449]),c_0_20]),c_0_40])]),c_0_29])).

cnf(c_0_453,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_450,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_451])).

cnf(c_0_454,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_452,c_0_94])).

cnf(c_0_455,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_453,c_0_96]),c_0_94])])).

cnf(c_0_456,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_454,c_0_455])).

cnf(c_0_457,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_449]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_458,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_456])).

cnf(c_0_459,negated_conjecture,
    ( ~ r1_waybel_9(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_448])])).

cnf(c_0_460,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_457,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_451])).

cnf(c_0_461,negated_conjecture,
    ( m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_458]),c_0_22]),c_0_20])]),c_0_459])).

cnf(c_0_462,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_460,c_0_96]),c_0_94])])).

cnf(c_0_463,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_461])).

cnf(c_0_464,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_462,c_0_463])).

cnf(c_0_465,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_454,c_0_464])).

cnf(c_0_466,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_465])).

cnf(c_0_467,negated_conjecture,
    ( m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_466]),c_0_22]),c_0_20])]),c_0_459])).

cnf(c_0_468,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_467])).

cnf(c_0_469,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_137,c_0_468])])).

cnf(c_0_470,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_469])).

cnf(c_0_471,negated_conjecture,
    ( m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_470]),c_0_22]),c_0_20])]),c_0_459])).

cnf(c_0_472,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_469])).

cnf(c_0_473,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_471]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_474,negated_conjecture,
    ( r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_472]),c_0_22]),c_0_20])]),c_0_459])).

cnf(c_0_475,negated_conjecture,
    ( r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_471]),c_0_20]),c_0_40])]),c_0_29])).

cnf(c_0_476,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_473,c_0_22]),c_0_23]),c_0_25]),c_0_474])]),c_0_28])).

cnf(c_0_477,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_475,c_0_94])).

cnf(c_0_478,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_476,c_0_96]),c_0_94])])).

cnf(c_0_479,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | ~ r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_469])).

cnf(c_0_480,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_477,c_0_478])).

cnf(c_0_481,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_471]),c_0_24]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_16]),c_0_39]),c_0_19]),c_0_40])])).

cnf(c_0_482,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_479,c_0_480])).

cnf(c_0_483,negated_conjecture,
    ( r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_481,c_0_22]),c_0_23]),c_0_25]),c_0_474])]),c_0_28])).

cnf(c_0_484,negated_conjecture,
    ( m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_482]),c_0_22]),c_0_20])]),c_0_459])).

cnf(c_0_485,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_483,c_0_96]),c_0_94])])).

cnf(c_0_486,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_484])).

cnf(c_0_487,negated_conjecture,
    ( r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_485,c_0_486])])).

cnf(c_0_488,negated_conjecture,
    ( r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_477,c_0_487])])).

cnf(c_0_489,negated_conjecture,
    ( r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_479,c_0_488])])).

cnf(c_0_490,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_489]),c_0_22]),c_0_20])]),c_0_459]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.67/0.87  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.67/0.87  # and selection function SelectNewComplexAHP.
% 0.67/0.87  #
% 0.67/0.87  # Preprocessing time       : 0.030 s
% 0.67/0.87  # Presaturation interreduction done
% 0.67/0.87  
% 0.67/0.87  # Proof found!
% 0.67/0.87  # SZS status Theorem
% 0.67/0.87  # SZS output start CNFRefutation
% 0.67/0.87  fof(t38_waybel_9, conjecture, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>(![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X2),X1,X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v10_waybel_0(X2,X1)=>(r1_waybel_9(X1,X2)&r2_hidden(k1_waybel_2(X1,X2),k10_yellow_6(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_waybel_9)).
% 0.67/0.87  fof(dt_l1_waybel_9, axiom, ![X1]:(l1_waybel_9(X1)=>(l1_pre_topc(X1)&l1_orders_2(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 0.67/0.87  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.67/0.87  fof(t30_waybel_9, axiom, ![X1]:(((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&v1_compts_1(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&r3_waybel_9(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_waybel_9)).
% 0.67/0.87  fof(t35_waybel_9, axiom, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(((![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X4),X1,X1))&v10_waybel_0(X3,X1))&r3_waybel_9(X1,X3,X2))=>X2=k1_waybel_2(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_waybel_9)).
% 0.67/0.87  fof(l48_waybel_9, axiom, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((((X3=X4&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X5),X1,X1)))&v10_waybel_0(X2,X1))&r3_waybel_9(X1,X2,X3))=>r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l48_waybel_9)).
% 0.67/0.87  fof(t30_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3))=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))&((r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))=>(X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow_0)).
% 0.67/0.87  fof(t33_waybel_9, axiom, ![X1]:(((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&v1_compts_1(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r3_waybel_9(X1,X2,X3)&r3_waybel_9(X1,X2,X4))=>X3=X4)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)=>r2_hidden(X3,k10_yellow_6(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_waybel_9)).
% 0.67/0.87  fof(d3_waybel_9, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_waybel_0(X2,X1)=>(r1_waybel_9(X1,X2)<=>r1_yellow_0(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_waybel_9)).
% 0.67/0.87  fof(l49_waybel_9, axiom, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((X3=X4&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X5),X1,X1)))&r3_waybel_9(X1,X2,X3))=>![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)=>r3_orders_2(X1,X4,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_waybel_9)).
% 0.67/0.87  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.67/0.87  fof(c_0_11, negated_conjecture, ~(![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>(![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X2),X1,X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v10_waybel_0(X2,X1)=>(r1_waybel_9(X1,X2)&r2_hidden(k1_waybel_2(X1,X2),k10_yellow_6(X1,X2)))))))), inference(assume_negation,[status(cth)],[t38_waybel_9])).
% 0.67/0.87  fof(c_0_12, plain, ![X18]:((l1_pre_topc(X18)|~l1_waybel_9(X18))&(l1_orders_2(X18)|~l1_waybel_9(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).
% 0.67/0.87  fof(c_0_13, negated_conjecture, ![X43]:(((((((((v2_pre_topc(esk8_0)&v8_pre_topc(esk8_0))&v3_orders_2(esk8_0))&v4_orders_2(esk8_0))&v5_orders_2(esk8_0))&v1_lattice3(esk8_0))&v2_lattice3(esk8_0))&v1_compts_1(esk8_0))&l1_waybel_9(esk8_0))&((~m1_subset_1(X43,u1_struct_0(esk8_0))|v5_pre_topc(k4_waybel_1(esk8_0,X43),esk8_0,esk8_0))&((((~v2_struct_0(esk9_0)&v4_orders_2(esk9_0))&v7_waybel_0(esk9_0))&l1_waybel_0(esk9_0,esk8_0))&(v10_waybel_0(esk9_0,esk8_0)&(~r1_waybel_9(esk8_0,esk9_0)|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).
% 0.67/0.87  fof(c_0_14, plain, ![X9]:(~l1_orders_2(X9)|(~v1_lattice3(X9)|~v2_struct_0(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.67/0.87  cnf(c_0_15, plain, (l1_orders_2(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.67/0.87  cnf(c_0_16, negated_conjecture, (l1_waybel_9(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.67/0.87  fof(c_0_17, plain, ![X30, X31]:((m1_subset_1(esk4_2(X30,X31),u1_struct_0(X30))|(v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~l1_waybel_0(X31,X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~v8_pre_topc(X30)|~v1_compts_1(X30)|~l1_pre_topc(X30)))&(r3_waybel_9(X30,X31,esk4_2(X30,X31))|(v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~l1_waybel_0(X31,X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~v8_pre_topc(X30)|~v1_compts_1(X30)|~l1_pre_topc(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_waybel_9])])])])])])).
% 0.67/0.87  cnf(c_0_18, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.67/0.87  cnf(c_0_19, negated_conjecture, (v1_lattice3(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.67/0.87  cnf(c_0_20, negated_conjecture, (l1_orders_2(esk8_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.67/0.87  cnf(c_0_21, plain, (m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.67/0.87  cnf(c_0_22, negated_conjecture, (l1_waybel_0(esk9_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.67/0.87  cnf(c_0_23, negated_conjecture, (v7_waybel_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.67/0.87  cnf(c_0_24, negated_conjecture, (v1_compts_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.67/0.87  cnf(c_0_25, negated_conjecture, (v4_orders_2(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.67/0.87  cnf(c_0_26, negated_conjecture, (v8_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.67/0.87  cnf(c_0_27, negated_conjecture, (v2_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.67/0.87  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.67/0.87  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.67/0.87  fof(c_0_30, plain, ![X38, X39, X40]:((m1_subset_1(esk7_3(X38,X39,X40),u1_struct_0(X38))|~v10_waybel_0(X40,X38)|~r3_waybel_9(X38,X40,X39)|X39=k1_waybel_2(X38,X40)|(v2_struct_0(X40)|~v4_orders_2(X40)|~v7_waybel_0(X40)|~l1_waybel_0(X40,X38))|~m1_subset_1(X39,u1_struct_0(X38))|(~v2_pre_topc(X38)|~v8_pre_topc(X38)|~v3_orders_2(X38)|~v4_orders_2(X38)|~v5_orders_2(X38)|~v1_lattice3(X38)|~v2_lattice3(X38)|~v1_compts_1(X38)|~l1_waybel_9(X38)))&(~v5_pre_topc(k4_waybel_1(X38,esk7_3(X38,X39,X40)),X38,X38)|~v10_waybel_0(X40,X38)|~r3_waybel_9(X38,X40,X39)|X39=k1_waybel_2(X38,X40)|(v2_struct_0(X40)|~v4_orders_2(X40)|~v7_waybel_0(X40)|~l1_waybel_0(X40,X38))|~m1_subset_1(X39,u1_struct_0(X38))|(~v2_pre_topc(X38)|~v8_pre_topc(X38)|~v3_orders_2(X38)|~v4_orders_2(X38)|~v5_orders_2(X38)|~v1_lattice3(X38)|~v2_lattice3(X38)|~v1_compts_1(X38)|~l1_waybel_9(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_waybel_9])])])])])])).
% 0.67/0.87  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~l1_pre_topc(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27])]), c_0_28]), c_0_29])).
% 0.67/0.87  cnf(c_0_32, plain, (l1_pre_topc(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.67/0.87  cnf(c_0_33, plain, (r3_waybel_9(X1,X2,esk4_2(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.67/0.87  fof(c_0_34, plain, ![X19, X20, X21, X22]:((m1_subset_1(esk2_4(X19,X20,X21,X22),u1_struct_0(X19))|X21!=X22|~v10_waybel_0(X20,X19)|~r3_waybel_9(X19,X20,X21)|r2_lattice3(X19,k2_relset_1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20)),X22)|~m1_subset_1(X22,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|(v2_struct_0(X20)|~v4_orders_2(X20)|~v7_waybel_0(X20)|~l1_waybel_0(X20,X19))|(~v2_pre_topc(X19)|~v8_pre_topc(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~v1_lattice3(X19)|~v2_lattice3(X19)|~v1_compts_1(X19)|~l1_waybel_9(X19)))&(~v5_pre_topc(k4_waybel_1(X19,esk2_4(X19,X20,X21,X22)),X19,X19)|X21!=X22|~v10_waybel_0(X20,X19)|~r3_waybel_9(X19,X20,X21)|r2_lattice3(X19,k2_relset_1(u1_struct_0(X20),u1_struct_0(X19),u1_waybel_0(X19,X20)),X22)|~m1_subset_1(X22,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|(v2_struct_0(X20)|~v4_orders_2(X20)|~v7_waybel_0(X20)|~l1_waybel_0(X20,X19))|(~v2_pre_topc(X19)|~v8_pre_topc(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~v1_lattice3(X19)|~v2_lattice3(X19)|~v1_compts_1(X19)|~l1_waybel_9(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l48_waybel_9])])])])])])).
% 0.67/0.87  cnf(c_0_35, plain, (m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))|X2=k1_waybel_2(X1,X3)|v2_struct_0(X3)|~v10_waybel_0(X3,X1)|~r3_waybel_9(X1,X3,X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.67/0.87  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_16])])).
% 0.67/0.87  cnf(c_0_37, negated_conjecture, (v2_lattice3(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.67/0.87  cnf(c_0_38, negated_conjecture, (v4_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.67/0.87  cnf(c_0_39, negated_conjecture, (v5_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.67/0.87  cnf(c_0_40, negated_conjecture, (v3_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.67/0.87  cnf(c_0_41, negated_conjecture, (r3_waybel_9(esk8_0,esk9_0,esk4_2(esk8_0,esk9_0))|~l1_pre_topc(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27])]), c_0_28]), c_0_29])).
% 0.67/0.87  cnf(c_0_42, plain, (X2=k1_waybel_2(X1,X3)|v2_struct_0(X3)|~v5_pre_topc(k4_waybel_1(X1,esk7_3(X1,X2,X3)),X1,X1)|~v10_waybel_0(X3,X1)|~r3_waybel_9(X1,X3,X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.67/0.87  cnf(c_0_43, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X1))|r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)|v2_struct_0(X2)|X3!=X4|~v10_waybel_0(X2,X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.67/0.87  fof(c_0_44, plain, ![X10, X11, X12, X13, X14]:(((r2_lattice3(X10,X12,X11)|(X11!=k1_yellow_0(X10,X12)|~r1_yellow_0(X10,X12))|~m1_subset_1(X11,u1_struct_0(X10))|(~v5_orders_2(X10)|~l1_orders_2(X10)))&(~m1_subset_1(X13,u1_struct_0(X10))|(~r2_lattice3(X10,X12,X13)|r1_orders_2(X10,X11,X13))|(X11!=k1_yellow_0(X10,X12)|~r1_yellow_0(X10,X12))|~m1_subset_1(X11,u1_struct_0(X10))|(~v5_orders_2(X10)|~l1_orders_2(X10))))&(((X11=k1_yellow_0(X10,X14)|(m1_subset_1(esk1_3(X10,X11,X14),u1_struct_0(X10))|~r2_lattice3(X10,X14,X11))|~m1_subset_1(X11,u1_struct_0(X10))|(~v5_orders_2(X10)|~l1_orders_2(X10)))&(r1_yellow_0(X10,X14)|(m1_subset_1(esk1_3(X10,X11,X14),u1_struct_0(X10))|~r2_lattice3(X10,X14,X11))|~m1_subset_1(X11,u1_struct_0(X10))|(~v5_orders_2(X10)|~l1_orders_2(X10))))&(((X11=k1_yellow_0(X10,X14)|(r2_lattice3(X10,X14,esk1_3(X10,X11,X14))|~r2_lattice3(X10,X14,X11))|~m1_subset_1(X11,u1_struct_0(X10))|(~v5_orders_2(X10)|~l1_orders_2(X10)))&(r1_yellow_0(X10,X14)|(r2_lattice3(X10,X14,esk1_3(X10,X11,X14))|~r2_lattice3(X10,X14,X11))|~m1_subset_1(X11,u1_struct_0(X10))|(~v5_orders_2(X10)|~l1_orders_2(X10))))&((X11=k1_yellow_0(X10,X14)|(~r1_orders_2(X10,X11,esk1_3(X10,X11,X14))|~r2_lattice3(X10,X14,X11))|~m1_subset_1(X11,u1_struct_0(X10))|(~v5_orders_2(X10)|~l1_orders_2(X10)))&(r1_yellow_0(X10,X14)|(~r1_orders_2(X10,X11,esk1_3(X10,X11,X14))|~r2_lattice3(X10,X14,X11))|~m1_subset_1(X11,u1_struct_0(X10))|(~v5_orders_2(X10)|~l1_orders_2(X10))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).
% 0.67/0.87  cnf(c_0_45, negated_conjecture, (esk4_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,X1)|m1_subset_1(esk7_3(esk8_0,esk4_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))|~v10_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_46, negated_conjecture, (v10_waybel_0(esk9_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.67/0.87  cnf(c_0_47, negated_conjecture, (r3_waybel_9(esk8_0,esk9_0,esk4_2(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_32]), c_0_16])])).
% 0.67/0.87  cnf(c_0_48, negated_conjecture, (esk4_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))|~v10_waybel_0(X1,esk8_0)|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk4_2(esk8_0,esk9_0),X1)),esk8_0,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_36]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_49, plain, (r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)|m1_subset_1(esk2_4(X1,X2,X3,X3),u1_struct_0(X1))|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~v10_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X2)|~v4_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X2,X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_43])).
% 0.67/0.87  cnf(c_0_50, plain, (r1_yellow_0(X1,X2)|m1_subset_1(esk1_3(X1,X3,X2),u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.67/0.87  cnf(c_0_51, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,X1),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.67/0.87  cnf(c_0_52, negated_conjecture, (esk4_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk4_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_23]), c_0_25]), c_0_22])]), c_0_28])).
% 0.67/0.87  cnf(c_0_53, negated_conjecture, (esk4_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk4_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_46]), c_0_47]), c_0_23]), c_0_25]), c_0_22])]), c_0_28])).
% 0.67/0.87  cnf(c_0_54, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X1)),esk4_2(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,X1,esk4_2(esk8_0,esk9_0),esk4_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))|~v10_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_36]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  fof(c_0_55, plain, ![X33, X34, X37]:((m1_subset_1(esk5_2(X33,X34),u1_struct_0(X33))|(~m1_subset_1(X37,u1_struct_0(X33))|(~r3_waybel_9(X33,X34,X37)|r2_hidden(X37,k10_yellow_6(X33,X34))))|(v2_struct_0(X34)|~v4_orders_2(X34)|~v7_waybel_0(X34)|~l1_waybel_0(X34,X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~v8_pre_topc(X33)|~v1_compts_1(X33)|~l1_pre_topc(X33)))&((m1_subset_1(esk6_2(X33,X34),u1_struct_0(X33))|(~m1_subset_1(X37,u1_struct_0(X33))|(~r3_waybel_9(X33,X34,X37)|r2_hidden(X37,k10_yellow_6(X33,X34))))|(v2_struct_0(X34)|~v4_orders_2(X34)|~v7_waybel_0(X34)|~l1_waybel_0(X34,X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~v8_pre_topc(X33)|~v1_compts_1(X33)|~l1_pre_topc(X33)))&(((r3_waybel_9(X33,X34,esk5_2(X33,X34))|(~m1_subset_1(X37,u1_struct_0(X33))|(~r3_waybel_9(X33,X34,X37)|r2_hidden(X37,k10_yellow_6(X33,X34))))|(v2_struct_0(X34)|~v4_orders_2(X34)|~v7_waybel_0(X34)|~l1_waybel_0(X34,X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~v8_pre_topc(X33)|~v1_compts_1(X33)|~l1_pre_topc(X33)))&(r3_waybel_9(X33,X34,esk6_2(X33,X34))|(~m1_subset_1(X37,u1_struct_0(X33))|(~r3_waybel_9(X33,X34,X37)|r2_hidden(X37,k10_yellow_6(X33,X34))))|(v2_struct_0(X34)|~v4_orders_2(X34)|~v7_waybel_0(X34)|~l1_waybel_0(X34,X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~v8_pre_topc(X33)|~v1_compts_1(X33)|~l1_pre_topc(X33))))&(esk5_2(X33,X34)!=esk6_2(X33,X34)|(~m1_subset_1(X37,u1_struct_0(X33))|(~r3_waybel_9(X33,X34,X37)|r2_hidden(X37,k10_yellow_6(X33,X34))))|(v2_struct_0(X34)|~v4_orders_2(X34)|~v7_waybel_0(X34)|~l1_waybel_0(X34,X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~v8_pre_topc(X33)|~v1_compts_1(X33)|~l1_pre_topc(X33)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t33_waybel_9])])])])])])).
% 0.67/0.87  cnf(c_0_56, negated_conjecture, (r1_yellow_0(esk8_0,X1)|m1_subset_1(esk1_3(esk8_0,esk4_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))|~r2_lattice3(esk8_0,X1,esk4_2(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_36]), c_0_39]), c_0_20])])).
% 0.67/0.87  cnf(c_0_57, negated_conjecture, (esk4_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.67/0.87  cnf(c_0_58, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk4_2(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,esk4_2(esk8_0,esk9_0),esk4_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_46]), c_0_47]), c_0_23]), c_0_25]), c_0_22])]), c_0_28])).
% 0.67/0.87  cnf(c_0_59, plain, (m1_subset_1(esk6_2(X1,X2),u1_struct_0(X1))|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.67/0.87  cnf(c_0_60, plain, (r1_yellow_0(X1,X2)|r2_lattice3(X1,X2,esk1_3(X1,X3,X2))|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.67/0.87  fof(c_0_61, plain, ![X16, X17]:((~r1_waybel_9(X16,X17)|r1_yellow_0(X16,k2_relset_1(u1_struct_0(X17),u1_struct_0(X16),u1_waybel_0(X16,X17)))|~l1_waybel_0(X17,X16)|~l1_orders_2(X16))&(~r1_yellow_0(X16,k2_relset_1(u1_struct_0(X17),u1_struct_0(X16),u1_waybel_0(X16,X17)))|r1_waybel_9(X16,X17)|~l1_waybel_0(X17,X16)|~l1_orders_2(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_waybel_9])])])])).
% 0.67/0.87  cnf(c_0_62, negated_conjecture, (r1_yellow_0(esk8_0,X1)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))|~r2_lattice3(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57]), c_0_57])).
% 0.67/0.87  cnf(c_0_63, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_57]), c_0_57]), c_0_57])).
% 0.67/0.87  cnf(c_0_64, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))|m1_subset_1(esk6_2(esk8_0,X1),u1_struct_0(esk8_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_pre_topc(esk8_0)|~l1_waybel_0(X1,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_36]), c_0_24]), c_0_26]), c_0_27])]), c_0_29])).
% 0.67/0.87  cnf(c_0_65, negated_conjecture, (r2_lattice3(esk8_0,X1,esk1_3(esk8_0,esk4_2(esk8_0,esk9_0),X1))|r1_yellow_0(esk8_0,X1)|~r2_lattice3(esk8_0,X1,esk4_2(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_36]), c_0_39]), c_0_20])])).
% 0.67/0.87  cnf(c_0_66, plain, (r1_waybel_9(X1,X2)|~r1_yellow_0(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))|~l1_waybel_0(X2,X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.67/0.87  cnf(c_0_67, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.67/0.87  cnf(c_0_68, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))|m1_subset_1(esk6_2(esk8_0,X1),u1_struct_0(esk8_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_32]), c_0_16])])).
% 0.67/0.87  cnf(c_0_69, negated_conjecture, (r2_lattice3(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),X1))|r1_yellow_0(esk8_0,X1)|~r2_lattice3(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_57]), c_0_57])).
% 0.67/0.87  cnf(c_0_70, plain, (m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.67/0.87  fof(c_0_71, plain, ![X24, X25, X26, X27, X29]:((m1_subset_1(esk3_4(X24,X25,X26,X27),u1_struct_0(X24))|X26!=X27|~r3_waybel_9(X24,X25,X26)|(~m1_subset_1(X29,u1_struct_0(X24))|(~r2_lattice3(X24,k2_relset_1(u1_struct_0(X25),u1_struct_0(X24),u1_waybel_0(X24,X25)),X29)|r3_orders_2(X24,X27,X29)))|~m1_subset_1(X27,u1_struct_0(X24))|~m1_subset_1(X26,u1_struct_0(X24))|(v2_struct_0(X25)|~v4_orders_2(X25)|~v7_waybel_0(X25)|~l1_waybel_0(X25,X24))|(~v2_pre_topc(X24)|~v8_pre_topc(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~v1_lattice3(X24)|~v2_lattice3(X24)|~v1_compts_1(X24)|~l1_waybel_9(X24)))&(~v5_pre_topc(k4_waybel_1(X24,esk3_4(X24,X25,X26,X27)),X24,X24)|X26!=X27|~r3_waybel_9(X24,X25,X26)|(~m1_subset_1(X29,u1_struct_0(X24))|(~r2_lattice3(X24,k2_relset_1(u1_struct_0(X25),u1_struct_0(X24),u1_waybel_0(X24,X25)),X29)|r3_orders_2(X24,X27,X29)))|~m1_subset_1(X27,u1_struct_0(X24))|~m1_subset_1(X26,u1_struct_0(X24))|(v2_struct_0(X25)|~v4_orders_2(X25)|~v7_waybel_0(X25)|~l1_waybel_0(X25,X24))|(~v2_pre_topc(X24)|~v8_pre_topc(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~v1_lattice3(X24)|~v2_lattice3(X24)|~v1_compts_1(X24)|~l1_waybel_9(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l49_waybel_9])])])])])])).
% 0.67/0.87  cnf(c_0_72, negated_conjecture, (~r1_waybel_9(esk8_0,esk9_0)|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.67/0.87  cnf(c_0_73, negated_conjecture, (r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_74, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_22]), c_0_47]), c_0_23]), c_0_25])]), c_0_28])).
% 0.67/0.87  cnf(c_0_75, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_69, c_0_63])).
% 0.67/0.87  cnf(c_0_76, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))|m1_subset_1(esk5_2(esk8_0,X1),u1_struct_0(esk8_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_pre_topc(esk8_0)|~l1_waybel_0(X1,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_36]), c_0_24]), c_0_26]), c_0_27])]), c_0_29])).
% 0.67/0.87  cnf(c_0_77, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X1))|r3_orders_2(X1,X4,X5)|v2_struct_0(X2)|X3!=X4|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X5,u1_struct_0(X1))|~r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.67/0.87  cnf(c_0_78, negated_conjecture, (m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.67/0.87  cnf(c_0_79, negated_conjecture, (r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(rw,[status(thm)],[c_0_74, c_0_57])).
% 0.67/0.87  cnf(c_0_80, negated_conjecture, (r1_waybel_9(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_75]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_81, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))|m1_subset_1(esk5_2(esk8_0,X1),u1_struct_0(esk8_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_32]), c_0_16])])).
% 0.67/0.87  fof(c_0_82, plain, ![X6, X7, X8]:((~r3_orders_2(X6,X7,X8)|r1_orders_2(X6,X7,X8)|(v2_struct_0(X6)|~v3_orders_2(X6)|~l1_orders_2(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))&(~r1_orders_2(X6,X7,X8)|r3_orders_2(X6,X7,X8)|(v2_struct_0(X6)|~v3_orders_2(X6)|~l1_orders_2(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.67/0.87  cnf(c_0_83, plain, (r3_orders_2(X1,X2,X3)|m1_subset_1(esk3_4(X1,X4,X2,X2),u1_struct_0(X1))|v2_struct_0(X4)|~r3_waybel_9(X1,X4,X2)|~v7_waybel_0(X4)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X4)|~v4_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X4,X1)|~r2_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_77])).
% 0.67/0.87  cnf(c_0_84, negated_conjecture, (m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.67/0.87  cnf(c_0_85, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_80])).
% 0.67/0.87  cnf(c_0_86, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_22]), c_0_47]), c_0_23]), c_0_25])]), c_0_28])).
% 0.67/0.87  cnf(c_0_87, plain, (r1_yellow_0(X1,X2)|~r1_orders_2(X1,X3,esk1_3(X1,X3,X2))|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.67/0.87  cnf(c_0_88, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.67/0.87  cnf(c_0_89, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_90, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_85, c_0_79])).
% 0.67/0.87  cnf(c_0_91, negated_conjecture, (r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(rw,[status(thm)],[c_0_86, c_0_57])).
% 0.67/0.87  cnf(c_0_92, negated_conjecture, (r1_yellow_0(esk8_0,X1)|~r2_lattice3(esk8_0,X1,esk4_2(esk8_0,esk9_0))|~r1_orders_2(esk8_0,esk4_2(esk8_0,esk9_0),esk1_3(esk8_0,esk4_2(esk8_0,esk9_0),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_36]), c_0_39]), c_0_20])])).
% 0.67/0.87  cnf(c_0_93, negated_conjecture, (r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_84]), c_0_20]), c_0_40])]), c_0_29])).
% 0.67/0.87  cnf(c_0_94, negated_conjecture, (m1_subset_1(k1_waybel_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(rw,[status(thm)],[c_0_36, c_0_57])).
% 0.67/0.87  cnf(c_0_95, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_90])).
% 0.67/0.87  cnf(c_0_96, negated_conjecture, (r3_waybel_9(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0))), inference(rw,[status(thm)],[c_0_47, c_0_57])).
% 0.67/0.87  cnf(c_0_97, negated_conjecture, (m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_78, c_0_91])).
% 0.67/0.87  cnf(c_0_98, negated_conjecture, (r1_yellow_0(esk8_0,X1)|~r2_lattice3(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0))|~r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_57]), c_0_57]), c_0_57])).
% 0.67/0.87  cnf(c_0_99, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.67/0.87  cnf(c_0_100, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_101, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_97]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_102, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_85, c_0_91])).
% 0.67/0.87  cnf(c_0_103, plain, (r3_orders_2(X1,X4,X5)|v2_struct_0(X2)|~v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X2,X3,X4)),X1,X1)|X3!=X4|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X5,u1_struct_0(X1))|~r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.67/0.87  cnf(c_0_104, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_98, c_0_63])).
% 0.67/0.87  cnf(c_0_105, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.67/0.87  cnf(c_0_106, negated_conjecture, (r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_97]), c_0_20]), c_0_40])]), c_0_29])).
% 0.67/0.87  cnf(c_0_107, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_102])).
% 0.67/0.87  cnf(c_0_108, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X4)|~r3_waybel_9(X1,X4,X2)|~v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X4,X2,X2)),X1,X1)|~v7_waybel_0(X4)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X4)|~v4_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X4,X1)|~r2_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_103])).
% 0.67/0.87  cnf(c_0_109, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.67/0.87  cnf(c_0_110, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_106, c_0_94])).
% 0.67/0.87  cnf(c_0_111, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_112, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_84]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_113, negated_conjecture, (r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_109]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_114, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 0.67/0.87  cnf(c_0_115, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_90])).
% 0.67/0.87  cnf(c_0_116, negated_conjecture, (m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_113]), c_0_79])).
% 0.67/0.87  cnf(c_0_117, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_104, c_0_114])).
% 0.67/0.87  cnf(c_0_118, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_119, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_116])).
% 0.67/0.87  cnf(c_0_120, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_97]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_121, negated_conjecture, (r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_117]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_122, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 0.67/0.87  cnf(c_0_123, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_102])).
% 0.67/0.87  cnf(c_0_124, negated_conjecture, (m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_121]), c_0_91])).
% 0.67/0.87  cnf(c_0_125, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_99, c_0_122])).
% 0.67/0.87  cnf(c_0_126, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_127, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_124])).
% 0.67/0.87  cnf(c_0_128, plain, (r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)|v2_struct_0(X2)|~v5_pre_topc(k4_waybel_1(X1,esk2_4(X1,X2,X3,X4)),X1,X1)|X3!=X4|~v10_waybel_0(X2,X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.67/0.87  cnf(c_0_129, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_104, c_0_125])).
% 0.67/0.87  cnf(c_0_130, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 0.67/0.87  cnf(c_0_131, plain, (r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~v10_waybel_0(X2,X1)|~v5_pre_topc(k4_waybel_1(X1,esk2_4(X1,X2,X3,X3)),X1,X1)|~v7_waybel_0(X2)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X2)|~v4_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X2,X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_128])).
% 0.67/0.87  cnf(c_0_132, negated_conjecture, (r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_129]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_133, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_110, c_0_130])).
% 0.67/0.87  cnf(c_0_134, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X1)),k1_waybel_2(esk8_0,esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0))|~v10_waybel_0(X1,esk8_0)|~v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_94]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_135, negated_conjecture, (m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_132]), c_0_79])).
% 0.67/0.87  cnf(c_0_136, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_104, c_0_133])).
% 0.67/0.87  cnf(c_0_137, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_46]), c_0_96]), c_0_23]), c_0_25]), c_0_22])]), c_0_28])).
% 0.67/0.87  cnf(c_0_138, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_135])).
% 0.67/0.87  cnf(c_0_139, negated_conjecture, (r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_136]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_140, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 0.67/0.87  cnf(c_0_141, negated_conjecture, (m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_139]), c_0_91])).
% 0.67/0.87  cnf(c_0_142, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_62, c_0_140])).
% 0.67/0.87  cnf(c_0_143, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_141])).
% 0.67/0.87  cnf(c_0_144, negated_conjecture, (r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_142]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_145, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_69, c_0_140])).
% 0.67/0.87  cnf(c_0_146, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_137, c_0_143])).
% 0.67/0.87  cnf(c_0_147, negated_conjecture, (m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_144]), c_0_79])).
% 0.67/0.87  cnf(c_0_148, negated_conjecture, (r1_waybel_9(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_145]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_149, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_62, c_0_146])).
% 0.67/0.87  cnf(c_0_150, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_147]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_151, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_148]), c_0_79])).
% 0.67/0.87  cnf(c_0_152, negated_conjecture, (r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_149]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_153, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_69, c_0_146])).
% 0.67/0.87  cnf(c_0_154, negated_conjecture, (r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_147]), c_0_20]), c_0_40])]), c_0_29])).
% 0.67/0.87  cnf(c_0_155, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_151])).
% 0.67/0.87  cnf(c_0_156, negated_conjecture, (m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_152]), c_0_91])).
% 0.67/0.87  cnf(c_0_157, negated_conjecture, (r1_waybel_9(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_153]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_158, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_154, c_0_94])).
% 0.67/0.87  cnf(c_0_159, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_160, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_156]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_161, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_157]), c_0_91])).
% 0.67/0.87  cnf(c_0_162, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_98, c_0_140])).
% 0.67/0.87  cnf(c_0_163, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_158, c_0_159])).
% 0.67/0.87  cnf(c_0_164, negated_conjecture, (r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_156]), c_0_20]), c_0_40])]), c_0_29])).
% 0.67/0.87  cnf(c_0_165, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_161])).
% 0.67/0.87  cnf(c_0_166, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_162, c_0_163])).
% 0.67/0.87  cnf(c_0_167, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_164, c_0_94])).
% 0.67/0.87  cnf(c_0_168, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_169, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_147]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_170, negated_conjecture, (r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_166]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_171, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_98, c_0_146])).
% 0.67/0.87  cnf(c_0_172, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_167, c_0_168])).
% 0.67/0.87  cnf(c_0_173, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_151])).
% 0.67/0.87  cnf(c_0_174, negated_conjecture, (m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_170]), c_0_79])).
% 0.67/0.87  cnf(c_0_175, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_171, c_0_172])).
% 0.67/0.87  cnf(c_0_176, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_177, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_174])).
% 0.67/0.87  cnf(c_0_178, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_156]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_179, negated_conjecture, (r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_175]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_180, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_176, c_0_177])).
% 0.67/0.87  cnf(c_0_181, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_161])).
% 0.67/0.87  cnf(c_0_182, negated_conjecture, (m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_179]), c_0_91])).
% 0.67/0.87  cnf(c_0_183, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_158, c_0_180])).
% 0.67/0.87  cnf(c_0_184, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_185, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_182])).
% 0.67/0.87  cnf(c_0_186, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_162, c_0_183])).
% 0.67/0.87  cnf(c_0_187, plain, (r3_waybel_9(X1,X2,esk6_2(X1,X2))|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.67/0.87  cnf(c_0_188, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_184, c_0_185])).
% 0.67/0.87  cnf(c_0_189, negated_conjecture, (r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_186]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_190, negated_conjecture, (r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))|r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,X1))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_pre_topc(esk8_0)|~l1_waybel_0(X1,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187, c_0_94]), c_0_24]), c_0_26]), c_0_27])]), c_0_29])).
% 0.67/0.87  cnf(c_0_191, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_167, c_0_188])).
% 0.67/0.87  cnf(c_0_192, negated_conjecture, (m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_189]), c_0_79])).
% 0.67/0.87  cnf(c_0_193, negated_conjecture, (r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))|r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,X1))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190, c_0_32]), c_0_16])])).
% 0.67/0.87  cnf(c_0_194, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_171, c_0_191])).
% 0.67/0.87  cnf(c_0_195, plain, (r3_waybel_9(X1,X2,esk5_2(X1,X2))|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.67/0.87  cnf(c_0_196, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,X1)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,esk9_0))|~v10_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_192]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_197, negated_conjecture, (r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))|r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193, c_0_22]), c_0_96]), c_0_23]), c_0_25])]), c_0_28])).
% 0.67/0.87  cnf(c_0_198, negated_conjecture, (r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_194]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_199, negated_conjecture, (r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))|r3_waybel_9(esk8_0,X1,esk5_2(esk8_0,X1))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_pre_topc(esk8_0)|~l1_waybel_0(X1,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_195, c_0_94]), c_0_24]), c_0_26]), c_0_27])]), c_0_29])).
% 0.67/0.87  cnf(c_0_200, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196, c_0_46]), c_0_23]), c_0_25]), c_0_22])]), c_0_28])).
% 0.67/0.87  cnf(c_0_201, negated_conjecture, (r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_78, c_0_197])).
% 0.67/0.87  cnf(c_0_202, negated_conjecture, (m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_198]), c_0_91])).
% 0.67/0.87  cnf(c_0_203, negated_conjecture, (r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))|r3_waybel_9(esk8_0,X1,esk5_2(esk8_0,X1))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,k1_waybel_2(esk8_0,esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199, c_0_32]), c_0_16])])).
% 0.67/0.87  cnf(c_0_204, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_200, c_0_201])).
% 0.67/0.87  cnf(c_0_205, negated_conjecture, (r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_85, c_0_197])).
% 0.67/0.87  cnf(c_0_206, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,X1)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk5_2(esk8_0,esk9_0))|~v10_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_202]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_207, negated_conjecture, (r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))|r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203, c_0_22]), c_0_96]), c_0_23]), c_0_25])]), c_0_28])).
% 0.67/0.87  cnf(c_0_208, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_204]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_209, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_200, c_0_205])).
% 0.67/0.87  cnf(c_0_210, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_206, c_0_46]), c_0_23]), c_0_25]), c_0_22])]), c_0_28])).
% 0.67/0.87  cnf(c_0_211, negated_conjecture, (r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_78, c_0_207])).
% 0.67/0.87  cnf(c_0_212, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_204]), c_0_20]), c_0_40])]), c_0_29])).
% 0.67/0.87  cnf(c_0_213, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_208, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_209])).
% 0.67/0.87  cnf(c_0_214, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_210, c_0_211])).
% 0.67/0.87  cnf(c_0_215, negated_conjecture, (r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_85, c_0_207])).
% 0.67/0.87  cnf(c_0_216, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_212, c_0_94])).
% 0.67/0.87  cnf(c_0_217, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_213, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_218, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_214]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_219, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_210, c_0_215])).
% 0.67/0.87  cnf(c_0_220, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_216, c_0_217])).
% 0.67/0.87  cnf(c_0_221, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_214]), c_0_20]), c_0_40])]), c_0_29])).
% 0.67/0.87  cnf(c_0_222, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_218, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_219])).
% 0.67/0.87  cnf(c_0_223, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_104, c_0_220])).
% 0.67/0.87  cnf(c_0_224, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_221, c_0_94])).
% 0.67/0.87  cnf(c_0_225, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_222, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_226, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_223]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_227, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_224, c_0_225])).
% 0.67/0.87  cnf(c_0_228, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_204]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_229, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_226])).
% 0.67/0.87  cnf(c_0_230, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_104, c_0_227])).
% 0.67/0.87  cnf(c_0_231, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_228, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_209])).
% 0.67/0.87  cnf(c_0_232, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_229, c_0_197]), c_0_200])).
% 0.67/0.87  cnf(c_0_233, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_230]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_234, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_231, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_235, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_232])).
% 0.67/0.87  cnf(c_0_236, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_214]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_237, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_233])).
% 0.67/0.87  cnf(c_0_238, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_234, c_0_235])).
% 0.67/0.87  cnf(c_0_239, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_236, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_219])).
% 0.67/0.87  cnf(c_0_240, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_237, c_0_207]), c_0_210])).
% 0.67/0.87  cnf(c_0_241, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_216, c_0_238])).
% 0.67/0.87  cnf(c_0_242, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_239, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_243, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_240])).
% 0.67/0.87  cnf(c_0_244, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_104, c_0_241])).
% 0.67/0.87  cnf(c_0_245, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_242, c_0_243])).
% 0.67/0.87  cnf(c_0_246, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_244]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_247, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_224, c_0_245])).
% 0.67/0.87  cnf(c_0_248, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_246])).
% 0.67/0.87  cnf(c_0_249, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_104, c_0_247])).
% 0.67/0.87  cnf(c_0_250, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_248, c_0_197]), c_0_200])).
% 0.67/0.87  cnf(c_0_251, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_249]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_252, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_250])).
% 0.67/0.87  cnf(c_0_253, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_251])).
% 0.67/0.87  cnf(c_0_254, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_137, c_0_252])).
% 0.67/0.87  cnf(c_0_255, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_253, c_0_207]), c_0_210])).
% 0.67/0.87  cnf(c_0_256, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_62, c_0_254])).
% 0.67/0.87  cnf(c_0_257, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_255])).
% 0.67/0.87  cnf(c_0_258, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_256]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_259, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_69, c_0_254])).
% 0.67/0.87  cnf(c_0_260, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_137, c_0_257])).
% 0.67/0.87  cnf(c_0_261, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_258])).
% 0.67/0.87  cnf(c_0_262, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_259]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_263, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_62, c_0_260])).
% 0.67/0.87  cnf(c_0_264, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_261, c_0_197]), c_0_200])).
% 0.67/0.87  cnf(c_0_265, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_262])).
% 0.67/0.87  cnf(c_0_266, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_263]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_267, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_69, c_0_260])).
% 0.67/0.87  cnf(c_0_268, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_264]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_269, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_265, c_0_197]), c_0_200])).
% 0.67/0.87  cnf(c_0_270, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_266])).
% 0.67/0.87  cnf(c_0_271, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_267]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_272, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_264]), c_0_20]), c_0_40])]), c_0_29])).
% 0.67/0.87  cnf(c_0_273, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_268, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_269])).
% 0.67/0.87  cnf(c_0_274, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_270, c_0_207]), c_0_210])).
% 0.67/0.87  cnf(c_0_275, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_271])).
% 0.67/0.87  cnf(c_0_276, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_272, c_0_94])).
% 0.67/0.87  cnf(c_0_277, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_273, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_278, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_274]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_279, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_275, c_0_207]), c_0_210])).
% 0.67/0.87  cnf(c_0_280, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_98, c_0_254])).
% 0.67/0.87  cnf(c_0_281, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_276, c_0_277])).
% 0.67/0.87  cnf(c_0_282, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_274]), c_0_20]), c_0_40])]), c_0_29])).
% 0.67/0.87  cnf(c_0_283, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_278, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_279])).
% 0.67/0.87  cnf(c_0_284, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_280, c_0_281])).
% 0.67/0.87  cnf(c_0_285, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_282, c_0_94])).
% 0.67/0.87  cnf(c_0_286, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_283, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_287, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_284]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_288, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_98, c_0_260])).
% 0.67/0.87  cnf(c_0_289, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_285, c_0_286])).
% 0.67/0.87  cnf(c_0_290, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_264]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_291, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_287])).
% 0.67/0.87  cnf(c_0_292, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_288, c_0_289])).
% 0.67/0.87  cnf(c_0_293, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_290, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_269])).
% 0.67/0.87  cnf(c_0_294, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_291, c_0_197]), c_0_200])).
% 0.67/0.87  cnf(c_0_295, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_292]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_296, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_293, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_297, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_294])).
% 0.67/0.87  cnf(c_0_298, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_274]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_299, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_295])).
% 0.67/0.87  cnf(c_0_300, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_296, c_0_297])).
% 0.67/0.87  cnf(c_0_301, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_298, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_279])).
% 0.67/0.87  cnf(c_0_302, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_299, c_0_207]), c_0_210])).
% 0.67/0.87  cnf(c_0_303, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_276, c_0_300])).
% 0.67/0.87  cnf(c_0_304, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_301, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_305, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_302])).
% 0.67/0.87  cnf(c_0_306, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_280, c_0_303])).
% 0.67/0.87  cnf(c_0_307, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_304, c_0_305])).
% 0.67/0.87  cnf(c_0_308, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_306]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_309, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_285, c_0_307])).
% 0.67/0.87  cnf(c_0_310, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,esk9_0))|~v10_waybel_0(X1,esk8_0)|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),X1)),esk8_0,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_192]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_311, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_308])).
% 0.67/0.87  cnf(c_0_312, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_288, c_0_309])).
% 0.67/0.87  cnf(c_0_313, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|~r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_310, c_0_46]), c_0_23]), c_0_25]), c_0_22])]), c_0_28])).
% 0.67/0.87  cnf(c_0_314, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_311, c_0_197]), c_0_200])).
% 0.67/0.87  cnf(c_0_315, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_312]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_316, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_313, c_0_201])).
% 0.67/0.87  cnf(c_0_317, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_51, c_0_314])).
% 0.67/0.87  cnf(c_0_318, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk5_2(esk8_0,esk9_0))|~v10_waybel_0(X1,esk8_0)|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),X1)),esk8_0,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_202]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_319, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_315])).
% 0.67/0.87  cnf(c_0_320, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_316, c_0_317])).
% 0.67/0.87  cnf(c_0_321, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_313, c_0_205])).
% 0.67/0.87  cnf(c_0_322, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|~r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_318, c_0_46]), c_0_23]), c_0_25]), c_0_22])]), c_0_28])).
% 0.67/0.87  cnf(c_0_323, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_319, c_0_207]), c_0_210])).
% 0.67/0.87  cnf(c_0_324, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_320]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_325, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_321, c_0_317])).
% 0.67/0.87  cnf(c_0_326, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_322, c_0_211])).
% 0.67/0.87  cnf(c_0_327, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_51, c_0_323])).
% 0.67/0.87  cnf(c_0_328, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_320]), c_0_20]), c_0_40])]), c_0_29])).
% 0.67/0.87  cnf(c_0_329, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_324, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_325])).
% 0.67/0.87  cnf(c_0_330, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_326, c_0_327])).
% 0.67/0.87  cnf(c_0_331, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_322, c_0_215])).
% 0.67/0.87  cnf(c_0_332, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_328, c_0_94])).
% 0.67/0.87  cnf(c_0_333, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_329, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_334, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_330]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_335, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_331, c_0_327])).
% 0.67/0.87  cnf(c_0_336, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_332, c_0_333])).
% 0.67/0.87  cnf(c_0_337, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_330]), c_0_20]), c_0_40])]), c_0_29])).
% 0.67/0.87  cnf(c_0_338, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_334, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_335])).
% 0.67/0.87  cnf(c_0_339, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_104, c_0_336])).
% 0.67/0.87  cnf(c_0_340, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_337, c_0_94])).
% 0.67/0.87  cnf(c_0_341, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_338, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_342, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_339]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_343, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_340, c_0_341])).
% 0.67/0.87  cnf(c_0_344, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_342])).
% 0.67/0.87  cnf(c_0_345, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_104, c_0_343])).
% 0.67/0.87  cnf(c_0_346, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_320]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_347, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_344, c_0_197])).
% 0.67/0.87  cnf(c_0_348, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_345]), c_0_22]), c_0_20])])).
% 0.67/0.87  cnf(c_0_349, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_346, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_325])).
% 0.67/0.87  cnf(c_0_350, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_313, c_0_347]), c_0_317])).
% 0.67/0.87  cnf(c_0_351, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_348])).
% 0.67/0.87  cnf(c_0_352, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_349, c_0_96]), c_0_94])])).
% 0.67/0.87  cnf(c_0_353, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_350])).
% 0.67/0.87  cnf(c_0_354, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_330]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.87  cnf(c_0_355, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_351, c_0_207])).
% 0.67/0.87  cnf(c_0_356, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_352, c_0_353])).
% 0.67/0.87  cnf(c_0_357, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_354, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_335])).
% 0.67/0.88  cnf(c_0_358, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_322, c_0_355]), c_0_327])).
% 0.67/0.88  cnf(c_0_359, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_332, c_0_356])).
% 0.67/0.88  cnf(c_0_360, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_357, c_0_96]), c_0_94])])).
% 0.67/0.88  cnf(c_0_361, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_358])).
% 0.67/0.88  cnf(c_0_362, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_104, c_0_359])).
% 0.67/0.88  cnf(c_0_363, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_360, c_0_361])).
% 0.67/0.88  cnf(c_0_364, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_362]), c_0_22]), c_0_20])])).
% 0.67/0.88  cnf(c_0_365, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_340, c_0_363])).
% 0.67/0.88  cnf(c_0_366, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_364])).
% 0.67/0.88  cnf(c_0_367, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_104, c_0_365])).
% 0.67/0.88  cnf(c_0_368, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_366, c_0_197])).
% 0.67/0.88  cnf(c_0_369, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_367]), c_0_22]), c_0_20])])).
% 0.67/0.88  cnf(c_0_370, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_313, c_0_368]), c_0_317])).
% 0.67/0.88  cnf(c_0_371, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_369])).
% 0.67/0.88  cnf(c_0_372, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_51, c_0_370])).
% 0.67/0.88  cnf(c_0_373, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_371, c_0_207])).
% 0.67/0.88  cnf(c_0_374, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_137, c_0_372])).
% 0.67/0.88  cnf(c_0_375, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_322, c_0_373]), c_0_327])).
% 0.67/0.88  cnf(c_0_376, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_62, c_0_374])).
% 0.67/0.88  cnf(c_0_377, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_51, c_0_375])).
% 0.67/0.88  cnf(c_0_378, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_376]), c_0_22]), c_0_20])])).
% 0.67/0.88  cnf(c_0_379, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))), inference(spm,[status(thm)],[c_0_69, c_0_374])).
% 0.67/0.88  cnf(c_0_380, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_137, c_0_377])).
% 0.67/0.88  cnf(c_0_381, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_378])).
% 0.67/0.88  cnf(c_0_382, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_379]), c_0_22]), c_0_20])])).
% 0.67/0.88  cnf(c_0_383, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_62, c_0_380])).
% 0.67/0.88  cnf(c_0_384, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_381, c_0_197])).
% 0.67/0.88  cnf(c_0_385, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_382])).
% 0.67/0.88  cnf(c_0_386, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_383]), c_0_22]), c_0_20])])).
% 0.67/0.88  cnf(c_0_387, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))), inference(spm,[status(thm)],[c_0_69, c_0_380])).
% 0.67/0.88  cnf(c_0_388, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_313, c_0_384]), c_0_317])).
% 0.67/0.88  cnf(c_0_389, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_385, c_0_197])).
% 0.67/0.88  cnf(c_0_390, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_386])).
% 0.67/0.88  cnf(c_0_391, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_387]), c_0_22]), c_0_20])])).
% 0.67/0.88  cnf(c_0_392, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_388]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.88  cnf(c_0_393, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_313, c_0_389]), c_0_317])).
% 0.67/0.88  cnf(c_0_394, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_390, c_0_207])).
% 0.67/0.88  cnf(c_0_395, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_391])).
% 0.67/0.88  cnf(c_0_396, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_388]), c_0_20]), c_0_40])]), c_0_29])).
% 0.67/0.88  cnf(c_0_397, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_392, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_393])).
% 0.67/0.88  cnf(c_0_398, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_322, c_0_394]), c_0_327])).
% 0.67/0.88  cnf(c_0_399, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_395, c_0_207])).
% 0.67/0.88  cnf(c_0_400, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_396, c_0_94])).
% 0.67/0.88  cnf(c_0_401, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_397, c_0_96]), c_0_94])])).
% 0.67/0.88  cnf(c_0_402, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_398]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.88  cnf(c_0_403, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_322, c_0_399]), c_0_327])).
% 0.67/0.88  cnf(c_0_404, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|~r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_98, c_0_374])).
% 0.67/0.88  cnf(c_0_405, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_400, c_0_401])).
% 0.67/0.88  cnf(c_0_406, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_398]), c_0_20]), c_0_40])]), c_0_29])).
% 0.67/0.88  cnf(c_0_407, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_402, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_403])).
% 0.67/0.88  cnf(c_0_408, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_404, c_0_405])).
% 0.67/0.88  cnf(c_0_409, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_406, c_0_94])).
% 0.67/0.88  cnf(c_0_410, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_407, c_0_96]), c_0_94])])).
% 0.67/0.88  cnf(c_0_411, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_408]), c_0_22]), c_0_20])])).
% 0.67/0.88  cnf(c_0_412, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|~r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_98, c_0_380])).
% 0.67/0.88  cnf(c_0_413, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_409, c_0_410])).
% 0.67/0.88  cnf(c_0_414, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_411])).
% 0.67/0.88  cnf(c_0_415, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_412, c_0_413])).
% 0.67/0.88  cnf(c_0_416, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_388]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.88  cnf(c_0_417, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_414, c_0_197])).
% 0.67/0.88  cnf(c_0_418, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_415]), c_0_22]), c_0_20])])).
% 0.67/0.88  cnf(c_0_419, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_416, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_393])).
% 0.67/0.88  cnf(c_0_420, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_313, c_0_417]), c_0_317])).
% 0.67/0.88  cnf(c_0_421, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_418])).
% 0.67/0.88  cnf(c_0_422, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_419, c_0_96]), c_0_94])])).
% 0.67/0.88  cnf(c_0_423, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_51, c_0_420])).
% 0.67/0.88  cnf(c_0_424, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_398]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.88  cnf(c_0_425, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_421, c_0_207])).
% 0.67/0.88  cnf(c_0_426, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_422, c_0_423])).
% 0.67/0.88  cnf(c_0_427, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_424, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_403])).
% 0.67/0.88  cnf(c_0_428, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_322, c_0_425]), c_0_327])).
% 0.67/0.88  cnf(c_0_429, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_400, c_0_426])).
% 0.67/0.88  cnf(c_0_430, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_427, c_0_96]), c_0_94])])).
% 0.67/0.88  cnf(c_0_431, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_51, c_0_428])).
% 0.67/0.88  cnf(c_0_432, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))), inference(spm,[status(thm)],[c_0_404, c_0_429])).
% 0.67/0.88  cnf(c_0_433, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_430, c_0_431])).
% 0.67/0.88  cnf(c_0_434, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_432]), c_0_22]), c_0_20])])).
% 0.67/0.88  cnf(c_0_435, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_409, c_0_433])).
% 0.67/0.88  cnf(c_0_436, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_434])).
% 0.67/0.88  cnf(c_0_437, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))), inference(spm,[status(thm)],[c_0_412, c_0_435])).
% 0.67/0.88  cnf(c_0_438, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_436, c_0_197])).
% 0.67/0.88  cnf(c_0_439, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r1_waybel_9(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_437]), c_0_22]), c_0_20])])).
% 0.67/0.88  cnf(c_0_440, plain, (r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|esk5_2(X1,X2)!=esk6_2(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.67/0.88  cnf(c_0_441, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_313, c_0_438]), c_0_317])).
% 0.67/0.88  cnf(c_0_442, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|~r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_439])).
% 0.67/0.88  cnf(c_0_443, negated_conjecture, (r2_hidden(X1,k10_yellow_6(esk8_0,esk9_0))|esk5_2(esk8_0,esk9_0)!=k1_waybel_2(esk8_0,esk9_0)|~r3_waybel_9(esk8_0,esk9_0,X1)|~l1_pre_topc(esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_440, c_0_441]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_22])]), c_0_28]), c_0_29])).
% 0.67/0.88  cnf(c_0_444, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_442, c_0_207])).
% 0.67/0.88  cnf(c_0_445, negated_conjecture, (r2_hidden(X1,k10_yellow_6(esk8_0,esk9_0))|esk5_2(esk8_0,esk9_0)!=k1_waybel_2(esk8_0,esk9_0)|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_443, c_0_32]), c_0_16])])).
% 0.67/0.88  cnf(c_0_446, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_2(esk8_0,esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_322, c_0_444]), c_0_327])).
% 0.67/0.88  cnf(c_0_447, negated_conjecture, (r2_hidden(X1,k10_yellow_6(esk8_0,esk9_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_445, c_0_446])])).
% 0.67/0.88  cnf(c_0_448, negated_conjecture, (r2_hidden(k1_waybel_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_447, c_0_96]), c_0_94])])).
% 0.67/0.88  cnf(c_0_449, negated_conjecture, (m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_448])])).
% 0.67/0.88  cnf(c_0_450, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_449]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.88  cnf(c_0_451, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_448])])).
% 0.67/0.88  cnf(c_0_452, negated_conjecture, (r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_449]), c_0_20]), c_0_40])]), c_0_29])).
% 0.67/0.88  cnf(c_0_453, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_450, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_451])).
% 0.67/0.88  cnf(c_0_454, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_452, c_0_94])).
% 0.67/0.88  cnf(c_0_455, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_453, c_0_96]), c_0_94])])).
% 0.67/0.88  cnf(c_0_456, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_454, c_0_455])).
% 0.67/0.88  cnf(c_0_457, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_449]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.88  cnf(c_0_458, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_104, c_0_456])).
% 0.67/0.88  cnf(c_0_459, negated_conjecture, (~r1_waybel_9(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_448])])).
% 0.67/0.88  cnf(c_0_460, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_457, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_451])).
% 0.67/0.88  cnf(c_0_461, negated_conjecture, (m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_458]), c_0_22]), c_0_20])]), c_0_459])).
% 0.67/0.88  cnf(c_0_462, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_460, c_0_96]), c_0_94])])).
% 0.67/0.88  cnf(c_0_463, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_461])).
% 0.67/0.88  cnf(c_0_464, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_462, c_0_463])).
% 0.67/0.88  cnf(c_0_465, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_454, c_0_464])).
% 0.67/0.88  cnf(c_0_466, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_104, c_0_465])).
% 0.67/0.88  cnf(c_0_467, negated_conjecture, (m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_466]), c_0_22]), c_0_20])]), c_0_459])).
% 0.67/0.88  cnf(c_0_468, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_51, c_0_467])).
% 0.67/0.88  cnf(c_0_469, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_2(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_137, c_0_468])])).
% 0.67/0.88  cnf(c_0_470, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_62, c_0_469])).
% 0.67/0.88  cnf(c_0_471, negated_conjecture, (m1_subset_1(esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_470]), c_0_22]), c_0_20])]), c_0_459])).
% 0.67/0.88  cnf(c_0_472, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))), inference(spm,[status(thm)],[c_0_69, c_0_469])).
% 0.67/0.88  cnf(c_0_473, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_471]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.88  cnf(c_0_474, negated_conjecture, (r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_472]), c_0_22]), c_0_20])]), c_0_459])).
% 0.67/0.88  cnf(c_0_475, negated_conjecture, (r1_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_471]), c_0_20]), c_0_40])]), c_0_29])).
% 0.67/0.88  cnf(c_0_476, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_473, c_0_22]), c_0_23]), c_0_25]), c_0_474])]), c_0_28])).
% 0.67/0.88  cnf(c_0_477, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_475, c_0_94])).
% 0.67/0.88  cnf(c_0_478, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_476, c_0_96]), c_0_94])])).
% 0.67/0.88  cnf(c_0_479, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|~r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_98, c_0_469])).
% 0.67/0.88  cnf(c_0_480, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_477, c_0_478])).
% 0.67/0.88  cnf(c_0_481, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r2_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_471]), c_0_24]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_16]), c_0_39]), c_0_19]), c_0_40])])).
% 0.67/0.88  cnf(c_0_482, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_479, c_0_480])).
% 0.67/0.88  cnf(c_0_483, negated_conjecture, (r3_orders_2(esk8_0,X1,esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_481, c_0_22]), c_0_23]), c_0_25]), c_0_474])]), c_0_28])).
% 0.67/0.88  cnf(c_0_484, negated_conjecture, (m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_482]), c_0_22]), c_0_20])]), c_0_459])).
% 0.67/0.88  cnf(c_0_485, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_483, c_0_96]), c_0_94])])).
% 0.67/0.88  cnf(c_0_486, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_2(esk8_0,esk9_0),k1_waybel_2(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_51, c_0_484])).
% 0.67/0.88  cnf(c_0_487, negated_conjecture, (r3_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_485, c_0_486])])).
% 0.67/0.88  cnf(c_0_488, negated_conjecture, (r1_orders_2(esk8_0,k1_waybel_2(esk8_0,esk9_0),esk1_3(esk8_0,k1_waybel_2(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_477, c_0_487])])).
% 0.67/0.88  cnf(c_0_489, negated_conjecture, (r1_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_479, c_0_488])])).
% 0.67/0.88  cnf(c_0_490, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_489]), c_0_22]), c_0_20])]), c_0_459]), ['proof']).
% 0.67/0.88  # SZS output end CNFRefutation
% 0.67/0.88  # Proof object total steps             : 491
% 0.67/0.88  # Proof object clause steps            : 468
% 0.67/0.88  # Proof object formula steps           : 23
% 0.67/0.88  # Proof object conjectures             : 446
% 0.67/0.88  # Proof object clause conjectures      : 443
% 0.67/0.88  # Proof object formula conjectures     : 3
% 0.67/0.88  # Proof object initial clauses used    : 37
% 0.67/0.88  # Proof object initial formulas used   : 11
% 0.67/0.88  # Proof object generating inferences   : 411
% 0.67/0.88  # Proof object simplifying inferences  : 957
% 0.67/0.88  # Training examples: 0 positive, 0 negative
% 0.67/0.88  # Parsed axioms                        : 11
% 0.67/0.88  # Removed by relevancy pruning/SinE    : 0
% 0.67/0.88  # Initial clauses                      : 44
% 0.67/0.88  # Removed in clause preprocessing      : 0
% 0.67/0.88  # Initial clauses in saturation        : 44
% 0.67/0.88  # Processed clauses                    : 2604
% 0.67/0.88  # ...of these trivial                  : 1
% 0.67/0.88  # ...subsumed                          : 386
% 0.67/0.88  # ...remaining for further processing  : 2217
% 0.67/0.88  # Other redundant clauses eliminated   : 6
% 0.67/0.88  # Clauses deleted for lack of memory   : 0
% 0.67/0.88  # Backward-subsumed                    : 1156
% 0.67/0.88  # Backward-rewritten                   : 847
% 0.67/0.88  # Generated clauses                    : 5752
% 0.67/0.88  # ...of the previous two non-trivial   : 5733
% 0.67/0.88  # Contextual simplify-reflections      : 129
% 0.67/0.88  # Paramodulations                      : 5744
% 0.67/0.88  # Factorizations                       : 0
% 0.67/0.88  # Equation resolutions                 : 6
% 0.67/0.88  # Propositional unsat checks           : 0
% 0.67/0.88  #    Propositional check models        : 0
% 0.67/0.88  #    Propositional check unsatisfiable : 0
% 0.67/0.88  #    Propositional clauses             : 0
% 0.67/0.88  #    Propositional clauses after purity: 0
% 0.67/0.88  #    Propositional unsat core size     : 0
% 0.67/0.88  #    Propositional preprocessing time  : 0.000
% 0.67/0.88  #    Propositional encoding time       : 0.000
% 0.67/0.88  #    Propositional solver time         : 0.000
% 0.67/0.88  #    Success case prop preproc time    : 0.000
% 0.67/0.88  #    Success case prop encoding time   : 0.000
% 0.67/0.88  #    Success case prop solver time     : 0.000
% 0.67/0.88  # Current number of processed clauses  : 162
% 0.67/0.88  #    Positive orientable unit clauses  : 38
% 0.67/0.88  #    Positive unorientable unit clauses: 0
% 0.67/0.88  #    Negative unit clauses             : 3
% 0.67/0.88  #    Non-unit-clauses                  : 121
% 0.67/0.88  # Current number of unprocessed clauses: 56
% 0.67/0.88  # ...number of literals in the above   : 256
% 0.67/0.88  # Current number of archived formulas  : 0
% 0.67/0.88  # Current number of archived clauses   : 2049
% 0.67/0.88  # Clause-clause subsumption calls (NU) : 323969
% 0.67/0.88  # Rec. Clause-clause subsumption calls : 29047
% 0.67/0.88  # Non-unit clause-clause subsumptions  : 1668
% 0.67/0.88  # Unit Clause-clause subsumption calls : 1369
% 0.67/0.88  # Rewrite failures with RHS unbound    : 0
% 0.67/0.88  # BW rewrite match attempts            : 58
% 0.67/0.88  # BW rewrite match successes           : 23
% 0.67/0.88  # Condensation attempts                : 0
% 0.67/0.88  # Condensation successes               : 0
% 0.67/0.88  # Termbank termtop insertions          : 411774
% 0.67/0.88  
% 0.67/0.88  # -------------------------------------------------
% 0.67/0.88  # User time                : 0.505 s
% 0.67/0.88  # System time              : 0.010 s
% 0.67/0.88  # Total time               : 0.515 s
% 0.67/0.88  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
