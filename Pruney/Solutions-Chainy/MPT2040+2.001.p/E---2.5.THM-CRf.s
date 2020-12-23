%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:48 EST 2020

% Result     : Theorem 0.65s
% Output     : CNFRefutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  432 (12894594618 expanded)
%              Number of clauses        :  411 (4172282241 expanded)
%              Number of leaves         :   10 (3133153207 expanded)
%              Depth                    :  142
%              Number of atoms          : 2261 (153032269231 expanded)
%              Number of equality atoms :  227 (421358384 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal clause size      :   65 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_waybel_9,conjecture,(
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
           => ( v11_waybel_0(X2,X1)
             => ( r2_waybel_9(X1,X2)
                & r2_hidden(k1_waybel_9(X1,X2),k10_yellow_6(X1,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_waybel_9)).

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

fof(t36_waybel_9,axiom,(
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
                  & v11_waybel_0(X3,X1)
                  & r3_waybel_9(X1,X3,X2) )
               => X2 = k1_waybel_9(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_waybel_9)).

fof(l51_waybel_9,axiom,(
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
                      & v11_waybel_0(X2,X1)
                      & r3_waybel_9(X1,X2,X3) )
                   => r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_waybel_9)).

fof(t16_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r2_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r1_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_yellow_0)).

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

fof(d4_waybel_9,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ( r2_waybel_9(X1,X2)
          <=> r2_yellow_0(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_waybel_9)).

fof(l52_waybel_9,axiom,(
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
                       => ( r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)
                         => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l52_waybel_9)).

fof(c_0_10,negated_conjecture,(
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
             => ( v11_waybel_0(X2,X1)
               => ( r2_waybel_9(X1,X2)
                  & r2_hidden(k1_waybel_9(X1,X2),k10_yellow_6(X1,X2)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t39_waybel_9])).

fof(c_0_11,plain,(
    ! [X28,X29] :
      ( ( m1_subset_1(esk5_2(X28,X29),u1_struct_0(X28))
        | v2_struct_0(X29)
        | ~ v4_orders_2(X29)
        | ~ v7_waybel_0(X29)
        | ~ l1_waybel_0(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ v8_pre_topc(X28)
        | ~ v1_compts_1(X28)
        | ~ l1_pre_topc(X28) )
      & ( r3_waybel_9(X28,X29,esk5_2(X28,X29))
        | v2_struct_0(X29)
        | ~ v4_orders_2(X29)
        | ~ v7_waybel_0(X29)
        | ~ l1_waybel_0(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ v8_pre_topc(X28)
        | ~ v1_compts_1(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_waybel_9])])])])])])).

fof(c_0_12,negated_conjecture,(
    ! [X41] :
      ( v2_pre_topc(esk9_0)
      & v8_pre_topc(esk9_0)
      & v3_orders_2(esk9_0)
      & v4_orders_2(esk9_0)
      & v5_orders_2(esk9_0)
      & v1_lattice3(esk9_0)
      & v2_lattice3(esk9_0)
      & v1_compts_1(esk9_0)
      & l1_waybel_9(esk9_0)
      & ( ~ m1_subset_1(X41,u1_struct_0(esk9_0))
        | v5_pre_topc(k4_waybel_1(esk9_0,X41),esk9_0,esk9_0) )
      & ~ v2_struct_0(esk10_0)
      & v4_orders_2(esk10_0)
      & v7_waybel_0(esk10_0)
      & l1_waybel_0(esk10_0,esk9_0)
      & v11_waybel_0(esk10_0,esk9_0)
      & ( ~ r2_waybel_9(esk9_0,esk10_0)
        | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).

fof(c_0_13,plain,(
    ! [X6] :
      ( ~ l1_orders_2(X6)
      | ~ v1_lattice3(X6)
      | ~ v2_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

cnf(c_0_14,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_waybel_0(esk10_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v7_waybel_0(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_compts_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v4_orders_2(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v8_pre_topc(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_22,plain,(
    ! [X16] :
      ( ( l1_pre_topc(X16)
        | ~ l1_waybel_9(X16) )
      & ( l1_orders_2(X16)
        | ~ l1_waybel_9(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).

cnf(c_0_23,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( v1_lattice3(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(esk9_0)
    | ~ l1_pre_topc(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_26,plain,
    ( l1_pre_topc(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( l1_waybel_9(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk9_0)
    | ~ l1_orders_2(esk9_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk5_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_30,plain,
    ( l1_orders_2(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X36,X37,X38] :
      ( ( m1_subset_1(esk8_3(X36,X37,X38),u1_struct_0(X36))
        | ~ v11_waybel_0(X38,X36)
        | ~ r3_waybel_9(X36,X38,X37)
        | X37 = k1_waybel_9(X36,X38)
        | v2_struct_0(X38)
        | ~ v4_orders_2(X38)
        | ~ v7_waybel_0(X38)
        | ~ l1_waybel_0(X38,X36)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | ~ v2_pre_topc(X36)
        | ~ v8_pre_topc(X36)
        | ~ v3_orders_2(X36)
        | ~ v4_orders_2(X36)
        | ~ v5_orders_2(X36)
        | ~ v1_lattice3(X36)
        | ~ v2_lattice3(X36)
        | ~ v1_compts_1(X36)
        | ~ l1_waybel_9(X36) )
      & ( ~ v5_pre_topc(k4_waybel_1(X36,esk8_3(X36,X37,X38)),X36,X36)
        | ~ v11_waybel_0(X38,X36)
        | ~ r3_waybel_9(X36,X38,X37)
        | X37 = k1_waybel_9(X36,X38)
        | v2_struct_0(X38)
        | ~ v4_orders_2(X38)
        | ~ v7_waybel_0(X38)
        | ~ l1_waybel_0(X38,X36)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | ~ v2_pre_topc(X36)
        | ~ v8_pre_topc(X36)
        | ~ v3_orders_2(X36)
        | ~ v4_orders_2(X36)
        | ~ v5_orders_2(X36)
        | ~ v1_lattice3(X36)
        | ~ v2_lattice3(X36)
        | ~ v1_compts_1(X36)
        | ~ l1_waybel_9(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_waybel_9])])])])])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk5_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ l1_orders_2(esk9_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( l1_orders_2(esk9_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

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
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_35,plain,(
    ! [X17,X18,X19,X20] :
      ( ( m1_subset_1(esk3_4(X17,X18,X19,X20),u1_struct_0(X17))
        | X19 != X20
        | ~ v11_waybel_0(X18,X17)
        | ~ r3_waybel_9(X17,X18,X19)
        | r1_lattice3(X17,k2_relset_1(u1_struct_0(X18),u1_struct_0(X17),u1_waybel_0(X17,X18)),X20)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | v2_struct_0(X18)
        | ~ v4_orders_2(X18)
        | ~ v7_waybel_0(X18)
        | ~ l1_waybel_0(X18,X17)
        | ~ v2_pre_topc(X17)
        | ~ v8_pre_topc(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ v1_lattice3(X17)
        | ~ v2_lattice3(X17)
        | ~ v1_compts_1(X17)
        | ~ l1_waybel_9(X17) )
      & ( ~ v5_pre_topc(k4_waybel_1(X17,esk3_4(X17,X18,X19,X20)),X17,X17)
        | X19 != X20
        | ~ v11_waybel_0(X18,X17)
        | ~ r3_waybel_9(X17,X18,X19)
        | r1_lattice3(X17,k2_relset_1(u1_struct_0(X18),u1_struct_0(X17),u1_waybel_0(X17,X18)),X20)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | v2_struct_0(X18)
        | ~ v4_orders_2(X18)
        | ~ v7_waybel_0(X18)
        | ~ l1_waybel_0(X18,X17)
        | ~ v2_pre_topc(X17)
        | ~ v8_pre_topc(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ v1_lattice3(X17)
        | ~ v2_lattice3(X17)
        | ~ v1_compts_1(X17)
        | ~ l1_waybel_9(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l51_waybel_9])])])])])])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk8_3(X1,X2,X3),u1_struct_0(X1))
    | X2 = k1_waybel_9(X1,X3)
    | v2_struct_0(X3)
    | ~ v11_waybel_0(X3,X1)
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
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_38,negated_conjecture,
    ( v2_lattice3(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( v4_orders_2(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( v3_orders_2(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( v5_orders_2(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,negated_conjecture,
    ( r3_waybel_9(esk9_0,esk10_0,esk5_2(esk9_0,esk10_0))
    | v2_struct_0(esk9_0)
    | ~ l1_pre_topc(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_33])])).

cnf(c_0_44,plain,
    ( X2 = k1_waybel_9(X1,X3)
    | v2_struct_0(X3)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk8_3(X1,X2,X3)),X1,X1)
    | ~ v11_waybel_0(X3,X1)
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

cnf(c_0_45,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X1))
    | r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)
    | v2_struct_0(X2)
    | X3 != X4
    | ~ v11_waybel_0(X2,X1)
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

fof(c_0_46,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( m1_subset_1(esk1_2(X7,X8),u1_struct_0(X7))
        | ~ r2_yellow_0(X7,X8)
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_lattice3(X7,X8,esk1_2(X7,X8))
        | ~ r2_yellow_0(X7,X8)
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_lattice3(X7,X8,X10)
        | r1_orders_2(X7,X10,esk1_2(X7,X8))
        | ~ r2_yellow_0(X7,X8)
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk2_3(X7,X11,X12),u1_struct_0(X7))
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | ~ r1_lattice3(X7,X11,X12)
        | r2_yellow_0(X7,X11)
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_lattice3(X7,X11,esk2_3(X7,X11,X12))
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | ~ r1_lattice3(X7,X11,X12)
        | r2_yellow_0(X7,X11)
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,esk2_3(X7,X11,X12),X12)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | ~ r1_lattice3(X7,X11,X12)
        | r2_yellow_0(X7,X11)
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_yellow_0])])])])])])).

cnf(c_0_47,negated_conjecture,
    ( esk5_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,X1)
    | m1_subset_1(esk8_3(esk9_0,esk5_2(esk9_0,esk10_0),X1),u1_struct_0(esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ v11_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_48,negated_conjecture,
    ( v11_waybel_0(esk10_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_49,negated_conjecture,
    ( r3_waybel_9(esk9_0,esk10_0,esk5_2(esk9_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_26]),c_0_27])]),c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( esk5_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ v11_waybel_0(X1,esk9_0)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk5_2(esk9_0,esk10_0),X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_37]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_51,plain,
    ( r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)
    | m1_subset_1(esk3_4(X1,X2,X3,X3),u1_struct_0(X1))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ v11_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v1_compts_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_9(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,X1),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_54,negated_conjecture,
    ( esk5_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk5_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_16]),c_0_18]),c_0_15])]),c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( esk5_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk5_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_48]),c_0_49]),c_0_16]),c_0_18]),c_0_15])]),c_0_21])).

cnf(c_0_56,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X1)),esk5_2(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,X1,esk5_2(esk9_0,esk10_0),esk5_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ v11_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_37]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

fof(c_0_57,plain,(
    ! [X31,X32,X35] :
      ( ( m1_subset_1(esk6_2(X31,X32),u1_struct_0(X31))
        | ~ m1_subset_1(X35,u1_struct_0(X31))
        | ~ r3_waybel_9(X31,X32,X35)
        | r2_hidden(X35,k10_yellow_6(X31,X32))
        | v2_struct_0(X32)
        | ~ v4_orders_2(X32)
        | ~ v7_waybel_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ v8_pre_topc(X31)
        | ~ v1_compts_1(X31)
        | ~ l1_pre_topc(X31) )
      & ( m1_subset_1(esk7_2(X31,X32),u1_struct_0(X31))
        | ~ m1_subset_1(X35,u1_struct_0(X31))
        | ~ r3_waybel_9(X31,X32,X35)
        | r2_hidden(X35,k10_yellow_6(X31,X32))
        | v2_struct_0(X32)
        | ~ v4_orders_2(X32)
        | ~ v7_waybel_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ v8_pre_topc(X31)
        | ~ v1_compts_1(X31)
        | ~ l1_pre_topc(X31) )
      & ( r3_waybel_9(X31,X32,esk6_2(X31,X32))
        | ~ m1_subset_1(X35,u1_struct_0(X31))
        | ~ r3_waybel_9(X31,X32,X35)
        | r2_hidden(X35,k10_yellow_6(X31,X32))
        | v2_struct_0(X32)
        | ~ v4_orders_2(X32)
        | ~ v7_waybel_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ v8_pre_topc(X31)
        | ~ v1_compts_1(X31)
        | ~ l1_pre_topc(X31) )
      & ( r3_waybel_9(X31,X32,esk7_2(X31,X32))
        | ~ m1_subset_1(X35,u1_struct_0(X31))
        | ~ r3_waybel_9(X31,X32,X35)
        | r2_hidden(X35,k10_yellow_6(X31,X32))
        | v2_struct_0(X32)
        | ~ v4_orders_2(X32)
        | ~ v7_waybel_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ v8_pre_topc(X31)
        | ~ v1_compts_1(X31)
        | ~ l1_pre_topc(X31) )
      & ( esk6_2(X31,X32) != esk7_2(X31,X32)
        | ~ m1_subset_1(X35,u1_struct_0(X31))
        | ~ r3_waybel_9(X31,X32,X35)
        | r2_hidden(X35,k10_yellow_6(X31,X32))
        | v2_struct_0(X32)
        | ~ v4_orders_2(X32)
        | ~ v7_waybel_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ v8_pre_topc(X31)
        | ~ v1_compts_1(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t33_waybel_9])])])])])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,X1,esk5_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,X1)
    | ~ r1_lattice3(esk9_0,X1,esk5_2(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_37]),c_0_41]),c_0_33])])).

cnf(c_0_59,negated_conjecture,
    ( esk5_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk5_2(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,esk5_2(esk9_0,esk10_0),esk5_2(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_48]),c_0_49]),c_0_16]),c_0_18]),c_0_15])]),c_0_21])).

cnf(c_0_61,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,plain,
    ( r1_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_63,plain,(
    ! [X14,X15] :
      ( ( ~ r2_waybel_9(X14,X15)
        | r2_yellow_0(X14,k2_relset_1(u1_struct_0(X15),u1_struct_0(X14),u1_waybel_0(X14,X15)))
        | ~ l1_waybel_0(X15,X14)
        | ~ l1_orders_2(X14) )
      & ( ~ r2_yellow_0(X14,k2_relset_1(u1_struct_0(X15),u1_struct_0(X14),u1_waybel_0(X14,X15)))
        | r2_waybel_9(X14,X15)
        | ~ l1_waybel_0(X15,X14)
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_waybel_9])])])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,X1)
    | ~ r1_lattice3(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_59]),c_0_59]),c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))
    | m1_subset_1(esk7_2(esk9_0,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(esk9_0)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_37]),c_0_17]),c_0_19]),c_0_20])]),c_0_43])).

cnf(c_0_67,negated_conjecture,
    ( r1_lattice3(esk9_0,X1,esk2_3(esk9_0,X1,esk5_2(esk9_0,esk10_0)))
    | r2_yellow_0(esk9_0,X1)
    | ~ r1_lattice3(esk9_0,X1,esk5_2(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_37]),c_0_41]),c_0_33])])).

cnf(c_0_68,plain,
    ( r2_waybel_9(X1,X2)
    | ~ r2_yellow_0(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))
    | m1_subset_1(esk7_2(esk9_0,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_26]),c_0_27])])).

cnf(c_0_71,negated_conjecture,
    ( r1_lattice3(esk9_0,X1,esk2_3(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0)))
    | r2_yellow_0(esk9_0,X1)
    | ~ r1_lattice3(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_59]),c_0_59])).

cnf(c_0_72,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_73,plain,(
    ! [X22,X23,X24,X25,X27] :
      ( ( m1_subset_1(esk4_4(X22,X23,X24,X25),u1_struct_0(X22))
        | X24 != X25
        | ~ r3_waybel_9(X22,X23,X24)
        | ~ m1_subset_1(X27,u1_struct_0(X22))
        | ~ r1_lattice3(X22,k2_relset_1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23)),X27)
        | r1_orders_2(X22,X27,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | v2_struct_0(X23)
        | ~ v4_orders_2(X23)
        | ~ v7_waybel_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | ~ v2_pre_topc(X22)
        | ~ v8_pre_topc(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ v1_lattice3(X22)
        | ~ v2_lattice3(X22)
        | ~ v1_compts_1(X22)
        | ~ l1_waybel_9(X22) )
      & ( ~ v5_pre_topc(k4_waybel_1(X22,esk4_4(X22,X23,X24,X25)),X22,X22)
        | X24 != X25
        | ~ r3_waybel_9(X22,X23,X24)
        | ~ m1_subset_1(X27,u1_struct_0(X22))
        | ~ r1_lattice3(X22,k2_relset_1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23)),X27)
        | r1_orders_2(X22,X27,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | v2_struct_0(X23)
        | ~ v4_orders_2(X23)
        | ~ v7_waybel_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | ~ v2_pre_topc(X22)
        | ~ v8_pre_topc(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ v1_lattice3(X22)
        | ~ v2_lattice3(X22)
        | ~ v1_compts_1(X22)
        | ~ l1_waybel_9(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l52_waybel_9])])])])])])).

cnf(c_0_74,negated_conjecture,
    ( ~ r2_waybel_9(esk9_0,esk10_0)
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_75,negated_conjecture,
    ( r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_15]),c_0_33])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_15]),c_0_49]),c_0_16]),c_0_18])]),c_0_21])).

cnf(c_0_77,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_65])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))
    | m1_subset_1(esk6_2(esk9_0,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(esk9_0)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_37]),c_0_17]),c_0_19]),c_0_20])]),c_0_43])).

cnf(c_0_79,plain,
    ( m1_subset_1(esk4_4(X1,X2,X3,X4),u1_struct_0(X1))
    | r1_orders_2(X1,X5,X4)
    | v2_struct_0(X2)
    | X3 != X4
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)
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
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(rw,[status(thm)],[c_0_76,c_0_59])).

cnf(c_0_82,negated_conjecture,
    ( r2_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_77]),c_0_15]),c_0_33])])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))
    | m1_subset_1(esk6_2(esk9_0,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_26]),c_0_27])])).

cnf(c_0_84,plain,
    ( r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_85,plain,
    ( r1_orders_2(X1,X2,X3)
    | m1_subset_1(esk4_4(X1,X4,X3,X3),u1_struct_0(X1))
    | v2_struct_0(X4)
    | ~ r3_waybel_9(X1,X4,X3)
    | ~ v7_waybel_0(X4)
    | ~ v1_compts_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v4_orders_2(X4)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_9(X1)
    | ~ l1_waybel_0(X4,X1)
    | ~ r1_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1) ),
    inference(er,[status(thm)],[c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_15]),c_0_49]),c_0_16]),c_0_18])]),c_0_21])).

cnf(c_0_89,negated_conjecture,
    ( r2_yellow_0(esk9_0,X1)
    | ~ r1_orders_2(esk9_0,esk2_3(esk9_0,X1,esk5_2(esk9_0,esk10_0)),esk5_2(esk9_0,esk10_0))
    | ~ r1_lattice3(esk9_0,X1,esk5_2(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_37]),c_0_41]),c_0_33])])).

cnf(c_0_90,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_91,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_81])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(rw,[status(thm)],[c_0_88,c_0_59])).

cnf(c_0_93,negated_conjecture,
    ( r2_yellow_0(esk9_0,X1)
    | ~ r1_orders_2(esk9_0,esk2_3(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | ~ r1_lattice3(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_59]),c_0_59]),c_0_59])).

cnf(c_0_94,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_15]),c_0_16]),c_0_18])]),c_0_21]),c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( r3_waybel_9(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_59])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(k1_waybel_9(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_59])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_92])).

cnf(c_0_98,plain,
    ( r1_orders_2(X1,X5,X4)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk4_4(X1,X2,X3,X4)),X1,X1)
    | X3 != X4
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)
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
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | ~ r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_65])).

cnf(c_0_100,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96])])).

cnf(c_0_101,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_97]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_102,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_92])).

cnf(c_0_103,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X4)
    | ~ r3_waybel_9(X1,X4,X3)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk4_4(X1,X4,X3,X3)),X1,X1)
    | ~ v7_waybel_0(X4)
    | ~ v1_compts_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v4_orders_2(X4)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_9(X1)
    | ~ l1_waybel_0(X4,X1)
    | ~ r1_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1) ),
    inference(er,[status(thm)],[c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_15]),c_0_16]),c_0_18])]),c_0_21]),c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_86]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_107,negated_conjecture,
    ( r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_104]),c_0_15]),c_0_33])])).

cnf(c_0_108,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_95]),c_0_96])])).

cnf(c_0_109,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_15]),c_0_16]),c_0_18])]),c_0_21]),c_0_91])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_107]),c_0_81])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_95]),c_0_96])])).

cnf(c_0_113,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_97]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_115,negated_conjecture,
    ( r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_111]),c_0_15]),c_0_33])])).

cnf(c_0_116,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_117,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_15]),c_0_16]),c_0_18])]),c_0_21]),c_0_102])).

cnf(c_0_118,negated_conjecture,
    ( m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_115]),c_0_92])).

cnf(c_0_119,plain,
    ( r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X2,X3,X4)),X1,X1)
    | X3 != X4
    | ~ v11_waybel_0(X2,X1)
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

cnf(c_0_120,negated_conjecture,
    ( m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_116])).

cnf(c_0_121,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_95]),c_0_96])])).

cnf(c_0_122,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_118])).

cnf(c_0_123,plain,
    ( r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ v11_waybel_0(X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X2,X3,X3)),X1,X1)
    | ~ v7_waybel_0(X2)
    | ~ v1_compts_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_9(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1) ),
    inference(er,[status(thm)],[c_0_119])).

cnf(c_0_124,negated_conjecture,
    ( r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_120]),c_0_15]),c_0_33])])).

cnf(c_0_125,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_126,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X1)),k1_waybel_9(esk9_0,esk10_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0))
    | ~ v11_waybel_0(X1,esk9_0)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_96]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_127,negated_conjecture,
    ( m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_124]),c_0_81])).

cnf(c_0_128,negated_conjecture,
    ( m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_125])).

cnf(c_0_129,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_48]),c_0_95]),c_0_16]),c_0_18]),c_0_15])]),c_0_21])).

cnf(c_0_130,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_127])).

cnf(c_0_131,negated_conjecture,
    ( r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_128]),c_0_15]),c_0_33])])).

cnf(c_0_132,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_133,negated_conjecture,
    ( m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_131]),c_0_92])).

cnf(c_0_134,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_132])).

cnf(c_0_135,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_133])).

cnf(c_0_136,negated_conjecture,
    ( r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_134]),c_0_15]),c_0_33])])).

cnf(c_0_137,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_132])).

cnf(c_0_138,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_135])).

cnf(c_0_139,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_136]),c_0_81])).

cnf(c_0_140,negated_conjecture,
    ( r2_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_137]),c_0_15]),c_0_33])])).

cnf(c_0_141,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_138])).

cnf(c_0_142,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_139]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_143,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_140]),c_0_81])).

cnf(c_0_144,negated_conjecture,
    ( r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_141]),c_0_15]),c_0_33])])).

cnf(c_0_145,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_138])).

cnf(c_0_146,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_15]),c_0_16]),c_0_18])]),c_0_21]),c_0_143])).

cnf(c_0_147,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_144]),c_0_92])).

cnf(c_0_148,negated_conjecture,
    ( r2_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_145]),c_0_15]),c_0_33])])).

cnf(c_0_149,negated_conjecture,
    ( m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | ~ r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_132])).

cnf(c_0_150,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_95]),c_0_96])])).

cnf(c_0_151,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_147]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_152,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_148]),c_0_92])).

cnf(c_0_153,negated_conjecture,
    ( m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_149,c_0_150])).

cnf(c_0_154,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_15]),c_0_16]),c_0_18])]),c_0_21]),c_0_152])).

cnf(c_0_155,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_139]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_156,negated_conjecture,
    ( r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_153]),c_0_15]),c_0_33])])).

cnf(c_0_157,negated_conjecture,
    ( m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | ~ r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_138])).

cnf(c_0_158,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_95]),c_0_96])])).

cnf(c_0_159,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_15]),c_0_16]),c_0_18])]),c_0_21]),c_0_143])).

cnf(c_0_160,negated_conjecture,
    ( m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_156]),c_0_81])).

cnf(c_0_161,negated_conjecture,
    ( m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_157,c_0_158])).

cnf(c_0_162,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_95]),c_0_96])])).

cnf(c_0_163,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_160])).

cnf(c_0_164,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_147]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_165,negated_conjecture,
    ( r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_161]),c_0_15]),c_0_33])])).

cnf(c_0_166,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_162,c_0_163])).

cnf(c_0_167,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_15]),c_0_16]),c_0_18])]),c_0_21]),c_0_152])).

cnf(c_0_168,negated_conjecture,
    ( m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_165]),c_0_92])).

cnf(c_0_169,negated_conjecture,
    ( m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_149,c_0_166])).

cnf(c_0_170,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_171,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_95]),c_0_96])])).

cnf(c_0_172,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_168])).

cnf(c_0_173,negated_conjecture,
    ( r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_169]),c_0_15]),c_0_33])])).

cnf(c_0_174,negated_conjecture,
    ( r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))
    | r3_waybel_9(esk9_0,X1,esk7_2(esk9_0,X1))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(esk9_0)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_96]),c_0_17]),c_0_19]),c_0_20])]),c_0_43])).

cnf(c_0_175,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_171,c_0_172])).

cnf(c_0_176,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_177,negated_conjecture,
    ( m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_173]),c_0_81])).

cnf(c_0_178,negated_conjecture,
    ( r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))
    | r3_waybel_9(esk9_0,X1,esk7_2(esk9_0,X1))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_26]),c_0_27])])).

cnf(c_0_179,negated_conjecture,
    ( m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_157,c_0_175])).

cnf(c_0_180,negated_conjecture,
    ( r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))
    | r3_waybel_9(esk9_0,X1,esk6_2(esk9_0,X1))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(esk9_0)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_37]),c_0_17]),c_0_19]),c_0_20])]),c_0_43])).

cnf(c_0_181,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,X1)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),X1),u1_struct_0(esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk7_2(esk9_0,esk10_0))
    | ~ v11_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_177]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_182,negated_conjecture,
    ( r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_15]),c_0_95]),c_0_16]),c_0_18])]),c_0_21])).

cnf(c_0_183,negated_conjecture,
    ( r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_179]),c_0_15]),c_0_33])])).

cnf(c_0_184,negated_conjecture,
    ( r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))
    | r3_waybel_9(esk9_0,X1,esk6_2(esk9_0,X1))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_26]),c_0_27])])).

cnf(c_0_185,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_48]),c_0_16]),c_0_18]),c_0_15])]),c_0_21])).

cnf(c_0_186,negated_conjecture,
    ( r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_182])).

cnf(c_0_187,negated_conjecture,
    ( m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_183]),c_0_92])).

cnf(c_0_188,negated_conjecture,
    ( r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_15]),c_0_49]),c_0_16]),c_0_18])]),c_0_21])).

cnf(c_0_189,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_185,c_0_186])).

cnf(c_0_190,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,X1)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),X1),u1_struct_0(esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk6_2(esk9_0,esk10_0))
    | ~ v11_waybel_0(X1,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_187]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_191,negated_conjecture,
    ( r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0)) ),
    inference(rw,[status(thm)],[c_0_188,c_0_59])).

cnf(c_0_192,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_189]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_193,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190,c_0_48]),c_0_16]),c_0_18]),c_0_15])]),c_0_21])).

cnf(c_0_194,negated_conjecture,
    ( r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_191])).

cnf(c_0_195,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_15]),c_0_16]),c_0_18])]),c_0_21])).

cnf(c_0_196,negated_conjecture,
    ( r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_182])).

cnf(c_0_197,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_193,c_0_194])).

cnf(c_0_198,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_195,c_0_196]),c_0_185])).

cnf(c_0_199,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_197]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_200,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_95]),c_0_96])])).

cnf(c_0_201,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199,c_0_15]),c_0_16]),c_0_18])]),c_0_21])).

cnf(c_0_202,negated_conjecture,
    ( r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_191])).

cnf(c_0_203,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_200])).

cnf(c_0_204,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_201,c_0_202]),c_0_193])).

cnf(c_0_205,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_189]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_206,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_203]),c_0_15]),c_0_33])])).

cnf(c_0_207,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_204,c_0_95]),c_0_96])])).

cnf(c_0_208,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205,c_0_15]),c_0_16]),c_0_18])]),c_0_21])).

cnf(c_0_209,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_206])).

cnf(c_0_210,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_207])).

cnf(c_0_211,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_208,c_0_196]),c_0_185])).

cnf(c_0_212,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_209,c_0_182]),c_0_185])).

cnf(c_0_213,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_197]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_214,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_210]),c_0_15]),c_0_33])])).

cnf(c_0_215,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_211,c_0_95]),c_0_96])])).

cnf(c_0_216,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_212])).

cnf(c_0_217,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_213,c_0_15]),c_0_16]),c_0_18])]),c_0_21])).

cnf(c_0_218,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_214])).

cnf(c_0_219,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_215,c_0_216])).

cnf(c_0_220,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_217,c_0_202]),c_0_193])).

cnf(c_0_221,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_218,c_0_191]),c_0_193])).

cnf(c_0_222,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_219])).

cnf(c_0_223,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_220,c_0_95]),c_0_96])])).

cnf(c_0_224,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_221])).

cnf(c_0_225,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_222]),c_0_15]),c_0_33])])).

cnf(c_0_226,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_223,c_0_224])).

cnf(c_0_227,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_225])).

cnf(c_0_228,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_226])).

cnf(c_0_229,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_227,c_0_182]),c_0_185])).

cnf(c_0_230,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_228]),c_0_15]),c_0_33])])).

cnf(c_0_231,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_229])).

cnf(c_0_232,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_230])).

cnf(c_0_233,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_231])).

cnf(c_0_234,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_232,c_0_191]),c_0_193])).

cnf(c_0_235,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_233])).

cnf(c_0_236,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_234])).

cnf(c_0_237,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_235]),c_0_15]),c_0_33])])).

cnf(c_0_238,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_233])).

cnf(c_0_239,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_236])).

cnf(c_0_240,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_237])).

cnf(c_0_241,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_238]),c_0_15]),c_0_33])])).

cnf(c_0_242,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_239])).

cnf(c_0_243,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_240,c_0_182]),c_0_185])).

cnf(c_0_244,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_241])).

cnf(c_0_245,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_242]),c_0_15]),c_0_33])])).

cnf(c_0_246,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_239])).

cnf(c_0_247,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_243]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_248,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_182]),c_0_185])).

cnf(c_0_249,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_245])).

cnf(c_0_250,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_246]),c_0_15]),c_0_33])])).

cnf(c_0_251,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_247,c_0_15]),c_0_16]),c_0_18])]),c_0_21]),c_0_248])).

cnf(c_0_252,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_249,c_0_191]),c_0_193])).

cnf(c_0_253,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_250])).

cnf(c_0_254,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | ~ r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_233])).

cnf(c_0_255,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_251,c_0_95]),c_0_96])])).

cnf(c_0_256,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_252]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_257,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_253,c_0_191]),c_0_193])).

cnf(c_0_258,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_254,c_0_255])).

cnf(c_0_259,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_256,c_0_15]),c_0_16]),c_0_18])]),c_0_21]),c_0_257])).

cnf(c_0_260,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_258]),c_0_15]),c_0_33])])).

cnf(c_0_261,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | ~ r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_239])).

cnf(c_0_262,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_259,c_0_95]),c_0_96])])).

cnf(c_0_263,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_243]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_264,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_260])).

cnf(c_0_265,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_261,c_0_262])).

cnf(c_0_266,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_263,c_0_15]),c_0_16]),c_0_18])]),c_0_21]),c_0_248])).

cnf(c_0_267,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_264,c_0_182]),c_0_185])).

cnf(c_0_268,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_265]),c_0_15]),c_0_33])])).

cnf(c_0_269,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_266,c_0_95]),c_0_96])])).

cnf(c_0_270,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_267])).

cnf(c_0_271,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_252]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_272,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_268])).

cnf(c_0_273,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_269,c_0_270])).

cnf(c_0_274,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_271,c_0_15]),c_0_16]),c_0_18])]),c_0_21]),c_0_257])).

cnf(c_0_275,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_272,c_0_191]),c_0_193])).

cnf(c_0_276,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_254,c_0_273])).

cnf(c_0_277,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_274,c_0_95]),c_0_96])])).

cnf(c_0_278,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_275])).

cnf(c_0_279,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_276]),c_0_15]),c_0_33])])).

cnf(c_0_280,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_277,c_0_278])).

cnf(c_0_281,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk7_2(esk9_0,esk10_0))
    | ~ v11_waybel_0(X1,esk9_0)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_177]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_282,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_279])).

cnf(c_0_283,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_261,c_0_280])).

cnf(c_0_284,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | ~ r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_281,c_0_48]),c_0_16]),c_0_18]),c_0_15])]),c_0_21])).

cnf(c_0_285,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_282,c_0_182]),c_0_185])).

cnf(c_0_286,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_283]),c_0_15]),c_0_33])])).

cnf(c_0_287,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_284,c_0_186])).

cnf(c_0_288,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_285])).

cnf(c_0_289,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk9_0,X1,esk6_2(esk9_0,esk10_0))
    | ~ v11_waybel_0(X1,esk9_0)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_187]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_290,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_286])).

cnf(c_0_291,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_287,c_0_288])).

cnf(c_0_292,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | ~ r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_289,c_0_48]),c_0_16]),c_0_18]),c_0_15])]),c_0_21])).

cnf(c_0_293,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_290,c_0_191]),c_0_193])).

cnf(c_0_294,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_291]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_295,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_292,c_0_194])).

cnf(c_0_296,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_293])).

cnf(c_0_297,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_294,c_0_15]),c_0_16]),c_0_18])]),c_0_21])).

cnf(c_0_298,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_295,c_0_296])).

cnf(c_0_299,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_297,c_0_196])).

cnf(c_0_300,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_298]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_301,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_299,c_0_95]),c_0_96])])).

cnf(c_0_302,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_300,c_0_15]),c_0_16]),c_0_18])]),c_0_21])).

cnf(c_0_303,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_301])).

cnf(c_0_304,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_302,c_0_202])).

cnf(c_0_305,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_291]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_306,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_303]),c_0_15]),c_0_33])])).

cnf(c_0_307,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_304,c_0_95]),c_0_96])])).

cnf(c_0_308,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_305,c_0_15]),c_0_16]),c_0_18])]),c_0_21])).

cnf(c_0_309,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_306]),c_0_182])).

cnf(c_0_310,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_307])).

cnf(c_0_311,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_308,c_0_196])).

cnf(c_0_312,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_284,c_0_309]),c_0_288])).

cnf(c_0_313,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_298]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_314,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_310]),c_0_15]),c_0_33])])).

cnf(c_0_315,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_311,c_0_95]),c_0_96])])).

cnf(c_0_316,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_312])).

cnf(c_0_317,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_313,c_0_15]),c_0_16]),c_0_18])]),c_0_21])).

cnf(c_0_318,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_314]),c_0_191])).

cnf(c_0_319,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_315,c_0_316])).

cnf(c_0_320,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_317,c_0_202])).

cnf(c_0_321,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_292,c_0_318]),c_0_296])).

cnf(c_0_322,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_319])).

cnf(c_0_323,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_320,c_0_95]),c_0_96])])).

cnf(c_0_324,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_321])).

cnf(c_0_325,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_322]),c_0_15]),c_0_33])])).

cnf(c_0_326,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_323,c_0_324])).

cnf(c_0_327,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_325]),c_0_182])).

cnf(c_0_328,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_326])).

cnf(c_0_329,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_284,c_0_327]),c_0_288])).

cnf(c_0_330,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_328]),c_0_15]),c_0_33])])).

cnf(c_0_331,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_329])).

cnf(c_0_332,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_330]),c_0_191])).

cnf(c_0_333,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_331])).

cnf(c_0_334,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_292,c_0_332]),c_0_296])).

cnf(c_0_335,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_333])).

cnf(c_0_336,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_334])).

cnf(c_0_337,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_335]),c_0_15]),c_0_33])])).

cnf(c_0_338,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_336])).

cnf(c_0_339,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_337])).

cnf(c_0_340,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_338])).

cnf(c_0_341,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_339,c_0_182])).

cnf(c_0_342,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_333])).

cnf(c_0_343,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_340]),c_0_15]),c_0_33])])).

cnf(c_0_344,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_284,c_0_341]),c_0_288])).

cnf(c_0_345,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_342]),c_0_15]),c_0_33])])).

cnf(c_0_346,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_343])).

cnf(c_0_347,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_344]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_348,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_345])).

cnf(c_0_349,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_346,c_0_191])).

cnf(c_0_350,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_338])).

cnf(c_0_351,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_347,c_0_15]),c_0_16]),c_0_18])]),c_0_21])).

cnf(c_0_352,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_348,c_0_182])).

cnf(c_0_353,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_292,c_0_349]),c_0_296])).

cnf(c_0_354,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_350]),c_0_15]),c_0_33])])).

cnf(c_0_355,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_351,c_0_352])).

cnf(c_0_356,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_353]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_357,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_354])).

cnf(c_0_358,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | ~ r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_333])).

cnf(c_0_359,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_355,c_0_95]),c_0_96])])).

cnf(c_0_360,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_356,c_0_15]),c_0_16]),c_0_18])]),c_0_21])).

cnf(c_0_361,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_357,c_0_191])).

cnf(c_0_362,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_358,c_0_359])).

cnf(c_0_363,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_360,c_0_361])).

cnf(c_0_364,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_344]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_365,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_362]),c_0_15]),c_0_33])])).

cnf(c_0_366,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | ~ r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_338])).

cnf(c_0_367,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_363,c_0_95]),c_0_96])])).

cnf(c_0_368,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_364,c_0_15]),c_0_16]),c_0_18])]),c_0_21])).

cnf(c_0_369,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_365]),c_0_182])).

cnf(c_0_370,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_366,c_0_367])).

cnf(c_0_371,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_368,c_0_352])).

cnf(c_0_372,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_284,c_0_369]),c_0_288])).

cnf(c_0_373,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_353]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_374,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r2_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_370]),c_0_15]),c_0_33])])).

cnf(c_0_375,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_371,c_0_96]),c_0_95])])).

cnf(c_0_376,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_372])).

cnf(c_0_377,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_373,c_0_15]),c_0_16]),c_0_18])]),c_0_21])).

cnf(c_0_378,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_374]),c_0_191])).

cnf(c_0_379,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_375,c_0_376])).

cnf(c_0_380,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_377,c_0_361])).

cnf(c_0_381,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_292,c_0_378]),c_0_296])).

cnf(c_0_382,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_358,c_0_379])).

cnf(c_0_383,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_380,c_0_96]),c_0_95])])).

cnf(c_0_384,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_381])).

cnf(c_0_385,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))
    | r2_waybel_9(esk9_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_382]),c_0_15]),c_0_33])])).

cnf(c_0_386,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_383,c_0_384])).

cnf(c_0_387,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_385]),c_0_182])).

cnf(c_0_388,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_366,c_0_386])).

cnf(c_0_389,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_390,negated_conjecture,
    ( esk7_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_284,c_0_387]),c_0_288])).

cnf(c_0_391,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))
    | r2_waybel_9(esk9_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_388]),c_0_15]),c_0_33])])).

cnf(c_0_392,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk9_0,esk10_0))
    | esk6_2(esk9_0,esk10_0) != k1_waybel_9(esk9_0,esk10_0)
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ l1_pre_topc(esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_389,c_0_390]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_15])]),c_0_21]),c_0_43])).

cnf(c_0_393,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0)
    | r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_391]),c_0_191])).

cnf(c_0_394,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk9_0,esk10_0))
    | esk6_2(esk9_0,esk10_0) != k1_waybel_9(esk9_0,esk10_0)
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_392,c_0_26]),c_0_27])])).

cnf(c_0_395,negated_conjecture,
    ( esk6_2(esk9_0,esk10_0) = k1_waybel_9(esk9_0,esk10_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_292,c_0_393]),c_0_296])).

cnf(c_0_396,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk9_0,esk10_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_394,c_0_395])])).

cnf(c_0_397,negated_conjecture,
    ( r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_396,c_0_95]),c_0_96])])).

cnf(c_0_398,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_397])])).

cnf(c_0_399,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_398]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_400,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_397])])).

cnf(c_0_401,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_399,c_0_15]),c_0_16]),c_0_18])]),c_0_21]),c_0_400])).

cnf(c_0_402,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_401,c_0_95]),c_0_96])])).

cnf(c_0_403,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_398]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_404,negated_conjecture,
    ( m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_402])).

cnf(c_0_405,negated_conjecture,
    ( ~ r2_waybel_9(esk9_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_397])])).

cnf(c_0_406,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_403,c_0_15]),c_0_16]),c_0_18])]),c_0_21]),c_0_400])).

cnf(c_0_407,negated_conjecture,
    ( m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_404]),c_0_15]),c_0_33])]),c_0_405])).

cnf(c_0_408,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_406,c_0_95]),c_0_96])])).

cnf(c_0_409,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_407])).

cnf(c_0_410,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_408,c_0_409])).

cnf(c_0_411,negated_conjecture,
    ( m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_410])).

cnf(c_0_412,negated_conjecture,
    ( m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_411]),c_0_15]),c_0_33])]),c_0_405])).

cnf(c_0_413,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_412])).

cnf(c_0_414,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_413])])).

cnf(c_0_415,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_414])).

cnf(c_0_416,negated_conjecture,
    ( m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_415]),c_0_15]),c_0_33])]),c_0_405])).

cnf(c_0_417,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_414])).

cnf(c_0_418,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_416]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_419,negated_conjecture,
    ( r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_417]),c_0_15]),c_0_33])]),c_0_405])).

cnf(c_0_420,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_418,c_0_15]),c_0_16]),c_0_18]),c_0_419])]),c_0_21])).

cnf(c_0_421,negated_conjecture,
    ( r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))
    | ~ r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_414])).

cnf(c_0_422,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_420,c_0_95]),c_0_96])])).

cnf(c_0_423,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk9_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk9_0)
    | ~ r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_416]),c_0_17]),c_0_38]),c_0_39]),c_0_40]),c_0_19]),c_0_20]),c_0_27]),c_0_41]),c_0_24])])).

cnf(c_0_424,negated_conjecture,
    ( m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))
    | r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_421,c_0_422])).

cnf(c_0_425,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)
    | ~ r3_waybel_9(esk9_0,esk10_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_423,c_0_15]),c_0_16]),c_0_18]),c_0_419])]),c_0_21])).

cnf(c_0_426,negated_conjecture,
    ( m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_424]),c_0_15]),c_0_33])]),c_0_405])).

cnf(c_0_427,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))
    | ~ v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_425,c_0_95]),c_0_96])])).

cnf(c_0_428,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_426])).

cnf(c_0_429,negated_conjecture,
    ( r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_427,c_0_428])])).

cnf(c_0_430,negated_conjecture,
    ( r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_421,c_0_429])])).

cnf(c_0_431,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_430]),c_0_15]),c_0_33])]),c_0_405]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.65/0.81  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.65/0.81  # and selection function SelectNewComplexAHP.
% 0.65/0.81  #
% 0.65/0.81  # Preprocessing time       : 0.030 s
% 0.65/0.81  # Presaturation interreduction done
% 0.65/0.81  
% 0.65/0.81  # Proof found!
% 0.65/0.81  # SZS status Theorem
% 0.65/0.81  # SZS output start CNFRefutation
% 0.65/0.81  fof(t39_waybel_9, conjecture, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>(![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X2),X1,X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v11_waybel_0(X2,X1)=>(r2_waybel_9(X1,X2)&r2_hidden(k1_waybel_9(X1,X2),k10_yellow_6(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_waybel_9)).
% 0.65/0.81  fof(t30_waybel_9, axiom, ![X1]:(((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&v1_compts_1(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&r3_waybel_9(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_waybel_9)).
% 0.65/0.81  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.65/0.81  fof(dt_l1_waybel_9, axiom, ![X1]:(l1_waybel_9(X1)=>(l1_pre_topc(X1)&l1_orders_2(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 0.65/0.81  fof(t36_waybel_9, axiom, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(((![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X4),X1,X1))&v11_waybel_0(X3,X1))&r3_waybel_9(X1,X3,X2))=>X2=k1_waybel_9(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_waybel_9)).
% 0.65/0.81  fof(l51_waybel_9, axiom, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((((X3=X4&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X5),X1,X1)))&v11_waybel_0(X2,X1))&r3_waybel_9(X1,X2,X3))=>r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_waybel_9)).
% 0.65/0.81  fof(t16_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(r2_yellow_0(X1,X2)<=>?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r1_lattice3(X1,X2,X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_yellow_0)).
% 0.65/0.81  fof(t33_waybel_9, axiom, ![X1]:(((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&v1_compts_1(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r3_waybel_9(X1,X2,X3)&r3_waybel_9(X1,X2,X4))=>X3=X4)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)=>r2_hidden(X3,k10_yellow_6(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_waybel_9)).
% 0.65/0.81  fof(d4_waybel_9, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_waybel_0(X2,X1)=>(r2_waybel_9(X1,X2)<=>r2_yellow_0(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_waybel_9)).
% 0.65/0.81  fof(l52_waybel_9, axiom, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((X3=X4&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X5),X1,X1)))&r3_waybel_9(X1,X2,X3))=>![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)=>r1_orders_2(X1,X5,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l52_waybel_9)).
% 0.65/0.81  fof(c_0_10, negated_conjecture, ~(![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>(![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X2),X1,X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v11_waybel_0(X2,X1)=>(r2_waybel_9(X1,X2)&r2_hidden(k1_waybel_9(X1,X2),k10_yellow_6(X1,X2)))))))), inference(assume_negation,[status(cth)],[t39_waybel_9])).
% 0.65/0.81  fof(c_0_11, plain, ![X28, X29]:((m1_subset_1(esk5_2(X28,X29),u1_struct_0(X28))|(v2_struct_0(X29)|~v4_orders_2(X29)|~v7_waybel_0(X29)|~l1_waybel_0(X29,X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~v8_pre_topc(X28)|~v1_compts_1(X28)|~l1_pre_topc(X28)))&(r3_waybel_9(X28,X29,esk5_2(X28,X29))|(v2_struct_0(X29)|~v4_orders_2(X29)|~v7_waybel_0(X29)|~l1_waybel_0(X29,X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~v8_pre_topc(X28)|~v1_compts_1(X28)|~l1_pre_topc(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_waybel_9])])])])])])).
% 0.65/0.81  fof(c_0_12, negated_conjecture, ![X41]:(((((((((v2_pre_topc(esk9_0)&v8_pre_topc(esk9_0))&v3_orders_2(esk9_0))&v4_orders_2(esk9_0))&v5_orders_2(esk9_0))&v1_lattice3(esk9_0))&v2_lattice3(esk9_0))&v1_compts_1(esk9_0))&l1_waybel_9(esk9_0))&((~m1_subset_1(X41,u1_struct_0(esk9_0))|v5_pre_topc(k4_waybel_1(esk9_0,X41),esk9_0,esk9_0))&((((~v2_struct_0(esk10_0)&v4_orders_2(esk10_0))&v7_waybel_0(esk10_0))&l1_waybel_0(esk10_0,esk9_0))&(v11_waybel_0(esk10_0,esk9_0)&(~r2_waybel_9(esk9_0,esk10_0)|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).
% 0.65/0.81  fof(c_0_13, plain, ![X6]:(~l1_orders_2(X6)|(~v1_lattice3(X6)|~v2_struct_0(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.65/0.81  cnf(c_0_14, plain, (m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.65/0.81  cnf(c_0_15, negated_conjecture, (l1_waybel_0(esk10_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.65/0.81  cnf(c_0_16, negated_conjecture, (v7_waybel_0(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.65/0.81  cnf(c_0_17, negated_conjecture, (v1_compts_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.65/0.81  cnf(c_0_18, negated_conjecture, (v4_orders_2(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.65/0.81  cnf(c_0_19, negated_conjecture, (v8_pre_topc(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.65/0.81  cnf(c_0_20, negated_conjecture, (v2_pre_topc(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.65/0.81  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.65/0.81  fof(c_0_22, plain, ![X16]:((l1_pre_topc(X16)|~l1_waybel_9(X16))&(l1_orders_2(X16)|~l1_waybel_9(X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).
% 0.65/0.81  cnf(c_0_23, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.65/0.81  cnf(c_0_24, negated_conjecture, (v1_lattice3(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.65/0.81  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk5_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(esk9_0)|~l1_pre_topc(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.65/0.81  cnf(c_0_26, plain, (l1_pre_topc(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.65/0.81  cnf(c_0_27, negated_conjecture, (l1_waybel_9(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.65/0.81  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk9_0)|~l1_orders_2(esk9_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.65/0.81  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk5_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.65/0.81  cnf(c_0_30, plain, (l1_orders_2(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.65/0.81  fof(c_0_31, plain, ![X36, X37, X38]:((m1_subset_1(esk8_3(X36,X37,X38),u1_struct_0(X36))|~v11_waybel_0(X38,X36)|~r3_waybel_9(X36,X38,X37)|X37=k1_waybel_9(X36,X38)|(v2_struct_0(X38)|~v4_orders_2(X38)|~v7_waybel_0(X38)|~l1_waybel_0(X38,X36))|~m1_subset_1(X37,u1_struct_0(X36))|(~v2_pre_topc(X36)|~v8_pre_topc(X36)|~v3_orders_2(X36)|~v4_orders_2(X36)|~v5_orders_2(X36)|~v1_lattice3(X36)|~v2_lattice3(X36)|~v1_compts_1(X36)|~l1_waybel_9(X36)))&(~v5_pre_topc(k4_waybel_1(X36,esk8_3(X36,X37,X38)),X36,X36)|~v11_waybel_0(X38,X36)|~r3_waybel_9(X36,X38,X37)|X37=k1_waybel_9(X36,X38)|(v2_struct_0(X38)|~v4_orders_2(X38)|~v7_waybel_0(X38)|~l1_waybel_0(X38,X36))|~m1_subset_1(X37,u1_struct_0(X36))|(~v2_pre_topc(X36)|~v8_pre_topc(X36)|~v3_orders_2(X36)|~v4_orders_2(X36)|~v5_orders_2(X36)|~v1_lattice3(X36)|~v2_lattice3(X36)|~v1_compts_1(X36)|~l1_waybel_9(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_waybel_9])])])])])])).
% 0.65/0.81  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk5_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~l1_orders_2(esk9_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.65/0.81  cnf(c_0_33, negated_conjecture, (l1_orders_2(esk9_0)), inference(spm,[status(thm)],[c_0_30, c_0_27])).
% 0.65/0.81  cnf(c_0_34, plain, (r3_waybel_9(X1,X2,esk5_2(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.65/0.81  fof(c_0_35, plain, ![X17, X18, X19, X20]:((m1_subset_1(esk3_4(X17,X18,X19,X20),u1_struct_0(X17))|X19!=X20|~v11_waybel_0(X18,X17)|~r3_waybel_9(X17,X18,X19)|r1_lattice3(X17,k2_relset_1(u1_struct_0(X18),u1_struct_0(X17),u1_waybel_0(X17,X18)),X20)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X18)|~v4_orders_2(X18)|~v7_waybel_0(X18)|~l1_waybel_0(X18,X17))|(~v2_pre_topc(X17)|~v8_pre_topc(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~v1_lattice3(X17)|~v2_lattice3(X17)|~v1_compts_1(X17)|~l1_waybel_9(X17)))&(~v5_pre_topc(k4_waybel_1(X17,esk3_4(X17,X18,X19,X20)),X17,X17)|X19!=X20|~v11_waybel_0(X18,X17)|~r3_waybel_9(X17,X18,X19)|r1_lattice3(X17,k2_relset_1(u1_struct_0(X18),u1_struct_0(X17),u1_waybel_0(X17,X18)),X20)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X18)|~v4_orders_2(X18)|~v7_waybel_0(X18)|~l1_waybel_0(X18,X17))|(~v2_pre_topc(X17)|~v8_pre_topc(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~v1_lattice3(X17)|~v2_lattice3(X17)|~v1_compts_1(X17)|~l1_waybel_9(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l51_waybel_9])])])])])])).
% 0.65/0.81  cnf(c_0_36, plain, (m1_subset_1(esk8_3(X1,X2,X3),u1_struct_0(X1))|X2=k1_waybel_9(X1,X3)|v2_struct_0(X3)|~v11_waybel_0(X3,X1)|~r3_waybel_9(X1,X3,X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.65/0.81  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk5_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33])])).
% 0.65/0.81  cnf(c_0_38, negated_conjecture, (v2_lattice3(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.65/0.81  cnf(c_0_39, negated_conjecture, (v4_orders_2(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.65/0.81  cnf(c_0_40, negated_conjecture, (v3_orders_2(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.65/0.81  cnf(c_0_41, negated_conjecture, (v5_orders_2(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.65/0.81  cnf(c_0_42, negated_conjecture, (r3_waybel_9(esk9_0,esk10_0,esk5_2(esk9_0,esk10_0))|v2_struct_0(esk9_0)|~l1_pre_topc(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.65/0.81  cnf(c_0_43, negated_conjecture, (~v2_struct_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_33])])).
% 0.65/0.81  cnf(c_0_44, plain, (X2=k1_waybel_9(X1,X3)|v2_struct_0(X3)|~v5_pre_topc(k4_waybel_1(X1,esk8_3(X1,X2,X3)),X1,X1)|~v11_waybel_0(X3,X1)|~r3_waybel_9(X1,X3,X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.65/0.81  cnf(c_0_45, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X1))|r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)|v2_struct_0(X2)|X3!=X4|~v11_waybel_0(X2,X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.65/0.81  fof(c_0_46, plain, ![X7, X8, X10, X11, X12]:((((m1_subset_1(esk1_2(X7,X8),u1_struct_0(X7))|~r2_yellow_0(X7,X8)|(~v5_orders_2(X7)|~l1_orders_2(X7)))&(r1_lattice3(X7,X8,esk1_2(X7,X8))|~r2_yellow_0(X7,X8)|(~v5_orders_2(X7)|~l1_orders_2(X7))))&(~m1_subset_1(X10,u1_struct_0(X7))|(~r1_lattice3(X7,X8,X10)|r1_orders_2(X7,X10,esk1_2(X7,X8)))|~r2_yellow_0(X7,X8)|(~v5_orders_2(X7)|~l1_orders_2(X7))))&((m1_subset_1(esk2_3(X7,X11,X12),u1_struct_0(X7))|(~m1_subset_1(X12,u1_struct_0(X7))|~r1_lattice3(X7,X11,X12))|r2_yellow_0(X7,X11)|(~v5_orders_2(X7)|~l1_orders_2(X7)))&((r1_lattice3(X7,X11,esk2_3(X7,X11,X12))|(~m1_subset_1(X12,u1_struct_0(X7))|~r1_lattice3(X7,X11,X12))|r2_yellow_0(X7,X11)|(~v5_orders_2(X7)|~l1_orders_2(X7)))&(~r1_orders_2(X7,esk2_3(X7,X11,X12),X12)|(~m1_subset_1(X12,u1_struct_0(X7))|~r1_lattice3(X7,X11,X12))|r2_yellow_0(X7,X11)|(~v5_orders_2(X7)|~l1_orders_2(X7)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_yellow_0])])])])])])).
% 0.65/0.81  cnf(c_0_47, negated_conjecture, (esk5_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,X1)|m1_subset_1(esk8_3(esk9_0,esk5_2(esk9_0,esk10_0),X1),u1_struct_0(esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~v11_waybel_0(X1,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_48, negated_conjecture, (v11_waybel_0(esk10_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.65/0.81  cnf(c_0_49, negated_conjecture, (r3_waybel_9(esk9_0,esk10_0,esk5_2(esk9_0,esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_26]), c_0_27])]), c_0_43])).
% 0.65/0.81  cnf(c_0_50, negated_conjecture, (esk5_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~v11_waybel_0(X1,esk9_0)|~v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk5_2(esk9_0,esk10_0),X1)),esk9_0,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_37]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_51, plain, (r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)|m1_subset_1(esk3_4(X1,X2,X3,X3),u1_struct_0(X1))|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~v11_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X2)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)), inference(er,[status(thm)],[c_0_45])).
% 0.65/0.81  cnf(c_0_52, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.65/0.81  cnf(c_0_53, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,X1),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.65/0.81  cnf(c_0_54, negated_conjecture, (esk5_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk5_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_16]), c_0_18]), c_0_15])]), c_0_21])).
% 0.65/0.81  cnf(c_0_55, negated_conjecture, (esk5_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|~v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk5_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_48]), c_0_49]), c_0_16]), c_0_18]), c_0_15])]), c_0_21])).
% 0.65/0.81  cnf(c_0_56, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X1)),esk5_2(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,X1,esk5_2(esk9_0,esk10_0),esk5_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~v11_waybel_0(X1,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_37]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  fof(c_0_57, plain, ![X31, X32, X35]:((m1_subset_1(esk6_2(X31,X32),u1_struct_0(X31))|(~m1_subset_1(X35,u1_struct_0(X31))|(~r3_waybel_9(X31,X32,X35)|r2_hidden(X35,k10_yellow_6(X31,X32))))|(v2_struct_0(X32)|~v4_orders_2(X32)|~v7_waybel_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~v8_pre_topc(X31)|~v1_compts_1(X31)|~l1_pre_topc(X31)))&((m1_subset_1(esk7_2(X31,X32),u1_struct_0(X31))|(~m1_subset_1(X35,u1_struct_0(X31))|(~r3_waybel_9(X31,X32,X35)|r2_hidden(X35,k10_yellow_6(X31,X32))))|(v2_struct_0(X32)|~v4_orders_2(X32)|~v7_waybel_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~v8_pre_topc(X31)|~v1_compts_1(X31)|~l1_pre_topc(X31)))&(((r3_waybel_9(X31,X32,esk6_2(X31,X32))|(~m1_subset_1(X35,u1_struct_0(X31))|(~r3_waybel_9(X31,X32,X35)|r2_hidden(X35,k10_yellow_6(X31,X32))))|(v2_struct_0(X32)|~v4_orders_2(X32)|~v7_waybel_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~v8_pre_topc(X31)|~v1_compts_1(X31)|~l1_pre_topc(X31)))&(r3_waybel_9(X31,X32,esk7_2(X31,X32))|(~m1_subset_1(X35,u1_struct_0(X31))|(~r3_waybel_9(X31,X32,X35)|r2_hidden(X35,k10_yellow_6(X31,X32))))|(v2_struct_0(X32)|~v4_orders_2(X32)|~v7_waybel_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~v8_pre_topc(X31)|~v1_compts_1(X31)|~l1_pre_topc(X31))))&(esk6_2(X31,X32)!=esk7_2(X31,X32)|(~m1_subset_1(X35,u1_struct_0(X31))|(~r3_waybel_9(X31,X32,X35)|r2_hidden(X35,k10_yellow_6(X31,X32))))|(v2_struct_0(X32)|~v4_orders_2(X32)|~v7_waybel_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~v8_pre_topc(X31)|~v1_compts_1(X31)|~l1_pre_topc(X31)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t33_waybel_9])])])])])])).
% 0.65/0.81  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,X1,esk5_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,X1)|~r1_lattice3(esk9_0,X1,esk5_2(esk9_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_37]), c_0_41]), c_0_33])])).
% 0.65/0.81  cnf(c_0_59, negated_conjecture, (esk5_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.65/0.81  cnf(c_0_60, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk5_2(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,esk5_2(esk9_0,esk10_0),esk5_2(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_48]), c_0_49]), c_0_16]), c_0_18]), c_0_15])]), c_0_21])).
% 0.65/0.81  cnf(c_0_61, plain, (m1_subset_1(esk7_2(X1,X2),u1_struct_0(X1))|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.65/0.81  cnf(c_0_62, plain, (r1_lattice3(X1,X2,esk2_3(X1,X2,X3))|r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.65/0.81  fof(c_0_63, plain, ![X14, X15]:((~r2_waybel_9(X14,X15)|r2_yellow_0(X14,k2_relset_1(u1_struct_0(X15),u1_struct_0(X14),u1_waybel_0(X14,X15)))|~l1_waybel_0(X15,X14)|~l1_orders_2(X14))&(~r2_yellow_0(X14,k2_relset_1(u1_struct_0(X15),u1_struct_0(X14),u1_waybel_0(X14,X15)))|r2_waybel_9(X14,X15)|~l1_waybel_0(X15,X14)|~l1_orders_2(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_waybel_9])])])])).
% 0.65/0.81  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,X1)|~r1_lattice3(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_59])).
% 0.65/0.81  cnf(c_0_65, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_59]), c_0_59]), c_0_59])).
% 0.65/0.81  cnf(c_0_66, negated_conjecture, (r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))|m1_subset_1(esk7_2(esk9_0,X1),u1_struct_0(esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_pre_topc(esk9_0)|~l1_waybel_0(X1,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_37]), c_0_17]), c_0_19]), c_0_20])]), c_0_43])).
% 0.65/0.81  cnf(c_0_67, negated_conjecture, (r1_lattice3(esk9_0,X1,esk2_3(esk9_0,X1,esk5_2(esk9_0,esk10_0)))|r2_yellow_0(esk9_0,X1)|~r1_lattice3(esk9_0,X1,esk5_2(esk9_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_37]), c_0_41]), c_0_33])])).
% 0.65/0.81  cnf(c_0_68, plain, (r2_waybel_9(X1,X2)|~r2_yellow_0(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))|~l1_waybel_0(X2,X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.65/0.81  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.65/0.81  cnf(c_0_70, negated_conjecture, (r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))|m1_subset_1(esk7_2(esk9_0,X1),u1_struct_0(esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_26]), c_0_27])])).
% 0.65/0.81  cnf(c_0_71, negated_conjecture, (r1_lattice3(esk9_0,X1,esk2_3(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0)))|r2_yellow_0(esk9_0,X1)|~r1_lattice3(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_59]), c_0_59])).
% 0.65/0.81  cnf(c_0_72, plain, (m1_subset_1(esk6_2(X1,X2),u1_struct_0(X1))|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.65/0.81  fof(c_0_73, plain, ![X22, X23, X24, X25, X27]:((m1_subset_1(esk4_4(X22,X23,X24,X25),u1_struct_0(X22))|X24!=X25|~r3_waybel_9(X22,X23,X24)|(~m1_subset_1(X27,u1_struct_0(X22))|(~r1_lattice3(X22,k2_relset_1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23)),X27)|r1_orders_2(X22,X27,X25)))|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|(v2_struct_0(X23)|~v4_orders_2(X23)|~v7_waybel_0(X23)|~l1_waybel_0(X23,X22))|(~v2_pre_topc(X22)|~v8_pre_topc(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~v1_lattice3(X22)|~v2_lattice3(X22)|~v1_compts_1(X22)|~l1_waybel_9(X22)))&(~v5_pre_topc(k4_waybel_1(X22,esk4_4(X22,X23,X24,X25)),X22,X22)|X24!=X25|~r3_waybel_9(X22,X23,X24)|(~m1_subset_1(X27,u1_struct_0(X22))|(~r1_lattice3(X22,k2_relset_1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23)),X27)|r1_orders_2(X22,X27,X25)))|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|(v2_struct_0(X23)|~v4_orders_2(X23)|~v7_waybel_0(X23)|~l1_waybel_0(X23,X22))|(~v2_pre_topc(X22)|~v8_pre_topc(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~v1_lattice3(X22)|~v2_lattice3(X22)|~v1_compts_1(X22)|~l1_waybel_9(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l52_waybel_9])])])])])])).
% 0.65/0.81  cnf(c_0_74, negated_conjecture, (~r2_waybel_9(esk9_0,esk10_0)|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.65/0.81  cnf(c_0_75, negated_conjecture, (r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_76, negated_conjecture, (r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_15]), c_0_49]), c_0_16]), c_0_18])]), c_0_21])).
% 0.65/0.81  cnf(c_0_77, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_71, c_0_65])).
% 0.65/0.81  cnf(c_0_78, negated_conjecture, (r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))|m1_subset_1(esk6_2(esk9_0,X1),u1_struct_0(esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_pre_topc(esk9_0)|~l1_waybel_0(X1,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_37]), c_0_17]), c_0_19]), c_0_20])]), c_0_43])).
% 0.65/0.81  cnf(c_0_79, plain, (m1_subset_1(esk4_4(X1,X2,X3,X4),u1_struct_0(X1))|r1_orders_2(X1,X5,X4)|v2_struct_0(X2)|X3!=X4|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X5,u1_struct_0(X1))|~r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.65/0.81  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.65/0.81  cnf(c_0_81, negated_conjecture, (r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(rw,[status(thm)],[c_0_76, c_0_59])).
% 0.65/0.81  cnf(c_0_82, negated_conjecture, (r2_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_77]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_83, negated_conjecture, (r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))|m1_subset_1(esk6_2(esk9_0,X1),u1_struct_0(esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_26]), c_0_27])])).
% 0.65/0.81  cnf(c_0_84, plain, (r2_yellow_0(X1,X2)|~r1_orders_2(X1,esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.65/0.81  cnf(c_0_85, plain, (r1_orders_2(X1,X2,X3)|m1_subset_1(esk4_4(X1,X4,X3,X3),u1_struct_0(X1))|v2_struct_0(X4)|~r3_waybel_9(X1,X4,X3)|~v7_waybel_0(X4)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X4)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X4,X1)|~r1_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)), inference(er,[status(thm)],[c_0_79])).
% 0.65/0.81  cnf(c_0_86, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.65/0.81  cnf(c_0_87, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_82])).
% 0.65/0.81  cnf(c_0_88, negated_conjecture, (r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_15]), c_0_49]), c_0_16]), c_0_18])]), c_0_21])).
% 0.65/0.81  cnf(c_0_89, negated_conjecture, (r2_yellow_0(esk9_0,X1)|~r1_orders_2(esk9_0,esk2_3(esk9_0,X1,esk5_2(esk9_0,esk10_0)),esk5_2(esk9_0,esk10_0))|~r1_lattice3(esk9_0,X1,esk5_2(esk9_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_37]), c_0_41]), c_0_33])])).
% 0.65/0.81  cnf(c_0_90, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_91, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_87, c_0_81])).
% 0.65/0.81  cnf(c_0_92, negated_conjecture, (r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(rw,[status(thm)],[c_0_88, c_0_59])).
% 0.65/0.81  cnf(c_0_93, negated_conjecture, (r2_yellow_0(esk9_0,X1)|~r1_orders_2(esk9_0,esk2_3(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|~r1_lattice3(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_59]), c_0_59]), c_0_59])).
% 0.65/0.81  cnf(c_0_94, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_15]), c_0_16]), c_0_18])]), c_0_21]), c_0_91])).
% 0.65/0.81  cnf(c_0_95, negated_conjecture, (r3_waybel_9(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0))), inference(rw,[status(thm)],[c_0_49, c_0_59])).
% 0.65/0.81  cnf(c_0_96, negated_conjecture, (m1_subset_1(k1_waybel_9(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(rw,[status(thm)],[c_0_37, c_0_59])).
% 0.65/0.81  cnf(c_0_97, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_80, c_0_92])).
% 0.65/0.81  cnf(c_0_98, plain, (r1_orders_2(X1,X5,X4)|v2_struct_0(X2)|~v5_pre_topc(k4_waybel_1(X1,esk4_4(X1,X2,X3,X4)),X1,X1)|X3!=X4|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X5,u1_struct_0(X1))|~r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.65/0.81  cnf(c_0_99, negated_conjecture, (m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|~r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_93, c_0_65])).
% 0.65/0.81  cnf(c_0_100, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_101, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_97]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_102, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_87, c_0_92])).
% 0.65/0.81  cnf(c_0_103, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X4)|~r3_waybel_9(X1,X4,X3)|~v5_pre_topc(k4_waybel_1(X1,esk4_4(X1,X4,X3,X3)),X1,X1)|~v7_waybel_0(X4)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X4)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X4,X1)|~r1_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)), inference(er,[status(thm)],[c_0_98])).
% 0.65/0.81  cnf(c_0_104, negated_conjecture, (m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.65/0.81  cnf(c_0_105, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_15]), c_0_16]), c_0_18])]), c_0_21]), c_0_102])).
% 0.65/0.81  cnf(c_0_106, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_86]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_107, negated_conjecture, (r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_104]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_108, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_109, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_15]), c_0_16]), c_0_18])]), c_0_21]), c_0_91])).
% 0.65/0.81  cnf(c_0_110, negated_conjecture, (m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_107]), c_0_81])).
% 0.65/0.81  cnf(c_0_111, negated_conjecture, (m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_108])).
% 0.65/0.81  cnf(c_0_112, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_113, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_110])).
% 0.65/0.81  cnf(c_0_114, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_97]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_115, negated_conjecture, (r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_111]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_116, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.65/0.81  cnf(c_0_117, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_15]), c_0_16]), c_0_18])]), c_0_21]), c_0_102])).
% 0.65/0.81  cnf(c_0_118, negated_conjecture, (m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_115]), c_0_92])).
% 0.65/0.81  cnf(c_0_119, plain, (r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)|v2_struct_0(X2)|~v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X2,X3,X4)),X1,X1)|X3!=X4|~v11_waybel_0(X2,X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.65/0.81  cnf(c_0_120, negated_conjecture, (m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_116])).
% 0.65/0.81  cnf(c_0_121, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_122, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_118])).
% 0.65/0.81  cnf(c_0_123, plain, (r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~v11_waybel_0(X2,X1)|~v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X2,X3,X3)),X1,X1)|~v7_waybel_0(X2)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X2)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)), inference(er,[status(thm)],[c_0_119])).
% 0.65/0.81  cnf(c_0_124, negated_conjecture, (r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_120]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_125, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 0.65/0.81  cnf(c_0_126, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X1)),k1_waybel_9(esk9_0,esk10_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0))|~v11_waybel_0(X1,esk9_0)|~v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_96]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_127, negated_conjecture, (m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_124]), c_0_81])).
% 0.65/0.81  cnf(c_0_128, negated_conjecture, (m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_125])).
% 0.65/0.81  cnf(c_0_129, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_48]), c_0_95]), c_0_16]), c_0_18]), c_0_15])]), c_0_21])).
% 0.65/0.81  cnf(c_0_130, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_127])).
% 0.65/0.81  cnf(c_0_131, negated_conjecture, (r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_128]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_132, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 0.65/0.81  cnf(c_0_133, negated_conjecture, (m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_131]), c_0_92])).
% 0.65/0.81  cnf(c_0_134, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_64, c_0_132])).
% 0.65/0.81  cnf(c_0_135, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_133])).
% 0.65/0.81  cnf(c_0_136, negated_conjecture, (r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_134]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_137, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_71, c_0_132])).
% 0.65/0.81  cnf(c_0_138, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_129, c_0_135])).
% 0.65/0.81  cnf(c_0_139, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_136]), c_0_81])).
% 0.65/0.81  cnf(c_0_140, negated_conjecture, (r2_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_137]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_141, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_64, c_0_138])).
% 0.65/0.81  cnf(c_0_142, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_139]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_143, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_140]), c_0_81])).
% 0.65/0.81  cnf(c_0_144, negated_conjecture, (r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_141]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_145, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_71, c_0_138])).
% 0.65/0.81  cnf(c_0_146, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_15]), c_0_16]), c_0_18])]), c_0_21]), c_0_143])).
% 0.65/0.81  cnf(c_0_147, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_144]), c_0_92])).
% 0.65/0.81  cnf(c_0_148, negated_conjecture, (r2_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_145]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_149, negated_conjecture, (m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|~r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_93, c_0_132])).
% 0.65/0.81  cnf(c_0_150, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_151, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_147]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_152, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_148]), c_0_92])).
% 0.65/0.81  cnf(c_0_153, negated_conjecture, (m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_149, c_0_150])).
% 0.65/0.81  cnf(c_0_154, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_15]), c_0_16]), c_0_18])]), c_0_21]), c_0_152])).
% 0.65/0.81  cnf(c_0_155, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_139]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_156, negated_conjecture, (r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_153]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_157, negated_conjecture, (m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|~r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_93, c_0_138])).
% 0.65/0.81  cnf(c_0_158, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_159, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_15]), c_0_16]), c_0_18])]), c_0_21]), c_0_143])).
% 0.65/0.81  cnf(c_0_160, negated_conjecture, (m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_156]), c_0_81])).
% 0.65/0.81  cnf(c_0_161, negated_conjecture, (m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_157, c_0_158])).
% 0.65/0.81  cnf(c_0_162, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_163, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_160])).
% 0.65/0.81  cnf(c_0_164, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_147]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_165, negated_conjecture, (r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_161]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_166, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_162, c_0_163])).
% 0.65/0.81  cnf(c_0_167, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_15]), c_0_16]), c_0_18])]), c_0_21]), c_0_152])).
% 0.65/0.81  cnf(c_0_168, negated_conjecture, (m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_165]), c_0_92])).
% 0.65/0.81  cnf(c_0_169, negated_conjecture, (m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_149, c_0_166])).
% 0.65/0.81  cnf(c_0_170, plain, (r3_waybel_9(X1,X2,esk7_2(X1,X2))|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.65/0.81  cnf(c_0_171, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_172, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_168])).
% 0.65/0.81  cnf(c_0_173, negated_conjecture, (r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_169]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_174, negated_conjecture, (r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))|r3_waybel_9(esk9_0,X1,esk7_2(esk9_0,X1))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_pre_topc(esk9_0)|~l1_waybel_0(X1,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_96]), c_0_17]), c_0_19]), c_0_20])]), c_0_43])).
% 0.65/0.81  cnf(c_0_175, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_171, c_0_172])).
% 0.65/0.81  cnf(c_0_176, plain, (r3_waybel_9(X1,X2,esk6_2(X1,X2))|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.65/0.81  cnf(c_0_177, negated_conjecture, (m1_subset_1(esk7_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_173]), c_0_81])).
% 0.65/0.81  cnf(c_0_178, negated_conjecture, (r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))|r3_waybel_9(esk9_0,X1,esk7_2(esk9_0,X1))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,k1_waybel_9(esk9_0,esk10_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_26]), c_0_27])])).
% 0.65/0.81  cnf(c_0_179, negated_conjecture, (m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_157, c_0_175])).
% 0.65/0.81  cnf(c_0_180, negated_conjecture, (r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))|r3_waybel_9(esk9_0,X1,esk6_2(esk9_0,X1))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_pre_topc(esk9_0)|~l1_waybel_0(X1,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176, c_0_37]), c_0_17]), c_0_19]), c_0_20])]), c_0_43])).
% 0.65/0.81  cnf(c_0_181, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,X1)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),X1),u1_struct_0(esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk7_2(esk9_0,esk10_0))|~v11_waybel_0(X1,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_177]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_182, negated_conjecture, (r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178, c_0_15]), c_0_95]), c_0_16]), c_0_18])]), c_0_21])).
% 0.65/0.81  cnf(c_0_183, negated_conjecture, (r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_179]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_184, negated_conjecture, (r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,X1))|r3_waybel_9(esk9_0,X1,esk6_2(esk9_0,X1))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk5_2(esk9_0,esk10_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180, c_0_26]), c_0_27])])).
% 0.65/0.81  cnf(c_0_185, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_48]), c_0_16]), c_0_18]), c_0_15])]), c_0_21])).
% 0.65/0.81  cnf(c_0_186, negated_conjecture, (r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_80, c_0_182])).
% 0.65/0.81  cnf(c_0_187, negated_conjecture, (m1_subset_1(esk6_2(esk9_0,esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_183]), c_0_92])).
% 0.65/0.81  cnf(c_0_188, negated_conjecture, (r2_hidden(esk5_2(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184, c_0_15]), c_0_49]), c_0_16]), c_0_18])]), c_0_21])).
% 0.65/0.81  cnf(c_0_189, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_185, c_0_186])).
% 0.65/0.81  cnf(c_0_190, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,X1)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),X1),u1_struct_0(esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk6_2(esk9_0,esk10_0))|~v11_waybel_0(X1,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_187]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_191, negated_conjecture, (r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))), inference(rw,[status(thm)],[c_0_188, c_0_59])).
% 0.65/0.81  cnf(c_0_192, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_189]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_193, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190, c_0_48]), c_0_16]), c_0_18]), c_0_15])]), c_0_21])).
% 0.65/0.81  cnf(c_0_194, negated_conjecture, (r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_80, c_0_191])).
% 0.65/0.81  cnf(c_0_195, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192, c_0_15]), c_0_16]), c_0_18])]), c_0_21])).
% 0.65/0.81  cnf(c_0_196, negated_conjecture, (r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_87, c_0_182])).
% 0.65/0.81  cnf(c_0_197, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_193, c_0_194])).
% 0.65/0.81  cnf(c_0_198, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_195, c_0_196]), c_0_185])).
% 0.65/0.81  cnf(c_0_199, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_197]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_200, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_201, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199, c_0_15]), c_0_16]), c_0_18])]), c_0_21])).
% 0.65/0.81  cnf(c_0_202, negated_conjecture, (r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_87, c_0_191])).
% 0.65/0.81  cnf(c_0_203, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_200])).
% 0.65/0.81  cnf(c_0_204, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_201, c_0_202]), c_0_193])).
% 0.65/0.81  cnf(c_0_205, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_189]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_206, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_203]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_207, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_204, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_208, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205, c_0_15]), c_0_16]), c_0_18])]), c_0_21])).
% 0.65/0.81  cnf(c_0_209, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_206])).
% 0.65/0.81  cnf(c_0_210, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_207])).
% 0.65/0.81  cnf(c_0_211, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_208, c_0_196]), c_0_185])).
% 0.65/0.81  cnf(c_0_212, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_209, c_0_182]), c_0_185])).
% 0.65/0.81  cnf(c_0_213, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_197]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_214, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_210]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_215, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_211, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_216, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_212])).
% 0.65/0.81  cnf(c_0_217, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_213, c_0_15]), c_0_16]), c_0_18])]), c_0_21])).
% 0.65/0.81  cnf(c_0_218, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_214])).
% 0.65/0.81  cnf(c_0_219, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_215, c_0_216])).
% 0.65/0.81  cnf(c_0_220, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_217, c_0_202]), c_0_193])).
% 0.65/0.81  cnf(c_0_221, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_218, c_0_191]), c_0_193])).
% 0.65/0.81  cnf(c_0_222, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_219])).
% 0.65/0.81  cnf(c_0_223, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_220, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_224, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_221])).
% 0.65/0.81  cnf(c_0_225, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_222]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_226, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_223, c_0_224])).
% 0.65/0.81  cnf(c_0_227, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_225])).
% 0.65/0.81  cnf(c_0_228, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_226])).
% 0.65/0.81  cnf(c_0_229, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_227, c_0_182]), c_0_185])).
% 0.65/0.81  cnf(c_0_230, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_228]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_231, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_229])).
% 0.65/0.81  cnf(c_0_232, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_230])).
% 0.65/0.81  cnf(c_0_233, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_129, c_0_231])).
% 0.65/0.81  cnf(c_0_234, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_232, c_0_191]), c_0_193])).
% 0.65/0.81  cnf(c_0_235, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_64, c_0_233])).
% 0.65/0.81  cnf(c_0_236, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_234])).
% 0.65/0.81  cnf(c_0_237, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_235]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_238, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_71, c_0_233])).
% 0.65/0.81  cnf(c_0_239, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_129, c_0_236])).
% 0.65/0.81  cnf(c_0_240, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_237])).
% 0.65/0.81  cnf(c_0_241, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_238]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_242, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_64, c_0_239])).
% 0.65/0.81  cnf(c_0_243, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_240, c_0_182]), c_0_185])).
% 0.65/0.81  cnf(c_0_244, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_241])).
% 0.65/0.81  cnf(c_0_245, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_242]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_246, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_71, c_0_239])).
% 0.65/0.81  cnf(c_0_247, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_243]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_248, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_182]), c_0_185])).
% 0.65/0.81  cnf(c_0_249, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_245])).
% 0.65/0.81  cnf(c_0_250, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_246]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_251, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_247, c_0_15]), c_0_16]), c_0_18])]), c_0_21]), c_0_248])).
% 0.65/0.81  cnf(c_0_252, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_249, c_0_191]), c_0_193])).
% 0.65/0.81  cnf(c_0_253, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_250])).
% 0.65/0.81  cnf(c_0_254, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|~r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_93, c_0_233])).
% 0.65/0.81  cnf(c_0_255, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_251, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_256, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_252]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_257, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_253, c_0_191]), c_0_193])).
% 0.65/0.81  cnf(c_0_258, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_254, c_0_255])).
% 0.65/0.81  cnf(c_0_259, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_256, c_0_15]), c_0_16]), c_0_18])]), c_0_21]), c_0_257])).
% 0.65/0.81  cnf(c_0_260, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_258]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_261, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|~r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_93, c_0_239])).
% 0.65/0.81  cnf(c_0_262, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_259, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_263, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_243]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_264, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_260])).
% 0.65/0.81  cnf(c_0_265, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_261, c_0_262])).
% 0.65/0.81  cnf(c_0_266, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_263, c_0_15]), c_0_16]), c_0_18])]), c_0_21]), c_0_248])).
% 0.65/0.81  cnf(c_0_267, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_264, c_0_182]), c_0_185])).
% 0.65/0.81  cnf(c_0_268, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_265]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_269, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_266, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_270, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_267])).
% 0.65/0.81  cnf(c_0_271, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_252]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_272, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_268])).
% 0.65/0.81  cnf(c_0_273, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_269, c_0_270])).
% 0.65/0.81  cnf(c_0_274, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_271, c_0_15]), c_0_16]), c_0_18])]), c_0_21]), c_0_257])).
% 0.65/0.81  cnf(c_0_275, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_272, c_0_191]), c_0_193])).
% 0.65/0.81  cnf(c_0_276, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_254, c_0_273])).
% 0.65/0.81  cnf(c_0_277, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_274, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_278, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_275])).
% 0.65/0.81  cnf(c_0_279, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_276]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_280, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_277, c_0_278])).
% 0.65/0.81  cnf(c_0_281, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk7_2(esk9_0,esk10_0))|~v11_waybel_0(X1,esk9_0)|~v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),X1)),esk9_0,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_177]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_282, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_279])).
% 0.65/0.81  cnf(c_0_283, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_261, c_0_280])).
% 0.65/0.81  cnf(c_0_284, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|~r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_281, c_0_48]), c_0_16]), c_0_18]), c_0_15])]), c_0_21])).
% 0.65/0.81  cnf(c_0_285, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_282, c_0_182]), c_0_185])).
% 0.65/0.81  cnf(c_0_286, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_283]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_287, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_284, c_0_186])).
% 0.65/0.81  cnf(c_0_288, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk7_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_53, c_0_285])).
% 0.65/0.81  cnf(c_0_289, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk9_0,X1,esk6_2(esk9_0,esk10_0))|~v11_waybel_0(X1,esk9_0)|~v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),X1)),esk9_0,esk9_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_187]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_290, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_286])).
% 0.65/0.81  cnf(c_0_291, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_287, c_0_288])).
% 0.65/0.81  cnf(c_0_292, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|~r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_289, c_0_48]), c_0_16]), c_0_18]), c_0_15])]), c_0_21])).
% 0.65/0.81  cnf(c_0_293, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_290, c_0_191]), c_0_193])).
% 0.65/0.81  cnf(c_0_294, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_291]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_295, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_292, c_0_194])).
% 0.65/0.81  cnf(c_0_296, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk8_3(esk9_0,esk6_2(esk9_0,esk10_0),esk10_0)),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_53, c_0_293])).
% 0.65/0.81  cnf(c_0_297, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_294, c_0_15]), c_0_16]), c_0_18])]), c_0_21])).
% 0.65/0.81  cnf(c_0_298, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_295, c_0_296])).
% 0.65/0.81  cnf(c_0_299, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_297, c_0_196])).
% 0.65/0.81  cnf(c_0_300, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_298]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_301, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_299, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_302, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_300, c_0_15]), c_0_16]), c_0_18])]), c_0_21])).
% 0.65/0.81  cnf(c_0_303, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_301])).
% 0.65/0.81  cnf(c_0_304, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_302, c_0_202])).
% 0.65/0.81  cnf(c_0_305, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_291]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_306, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_303]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_307, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_304, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_308, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_305, c_0_15]), c_0_16]), c_0_18])]), c_0_21])).
% 0.65/0.81  cnf(c_0_309, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_306]), c_0_182])).
% 0.65/0.81  cnf(c_0_310, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_307])).
% 0.65/0.81  cnf(c_0_311, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_308, c_0_196])).
% 0.65/0.81  cnf(c_0_312, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_284, c_0_309]), c_0_288])).
% 0.65/0.81  cnf(c_0_313, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_298]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_314, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_310]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_315, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_311, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_316, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_312])).
% 0.65/0.81  cnf(c_0_317, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_313, c_0_15]), c_0_16]), c_0_18])]), c_0_21])).
% 0.65/0.81  cnf(c_0_318, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_314]), c_0_191])).
% 0.65/0.81  cnf(c_0_319, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_315, c_0_316])).
% 0.65/0.81  cnf(c_0_320, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_317, c_0_202])).
% 0.65/0.81  cnf(c_0_321, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_292, c_0_318]), c_0_296])).
% 0.65/0.81  cnf(c_0_322, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_319])).
% 0.65/0.81  cnf(c_0_323, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_320, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_324, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_321])).
% 0.65/0.81  cnf(c_0_325, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_322]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_326, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_323, c_0_324])).
% 0.65/0.81  cnf(c_0_327, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_325]), c_0_182])).
% 0.65/0.81  cnf(c_0_328, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_326])).
% 0.65/0.81  cnf(c_0_329, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_284, c_0_327]), c_0_288])).
% 0.65/0.81  cnf(c_0_330, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_328]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_331, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_53, c_0_329])).
% 0.65/0.81  cnf(c_0_332, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_330]), c_0_191])).
% 0.65/0.81  cnf(c_0_333, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_129, c_0_331])).
% 0.65/0.81  cnf(c_0_334, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_292, c_0_332]), c_0_296])).
% 0.65/0.81  cnf(c_0_335, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_64, c_0_333])).
% 0.65/0.81  cnf(c_0_336, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_53, c_0_334])).
% 0.65/0.81  cnf(c_0_337, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_335]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_338, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_129, c_0_336])).
% 0.65/0.81  cnf(c_0_339, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_337])).
% 0.65/0.81  cnf(c_0_340, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_64, c_0_338])).
% 0.65/0.81  cnf(c_0_341, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_339, c_0_182])).
% 0.65/0.81  cnf(c_0_342, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_71, c_0_333])).
% 0.65/0.81  cnf(c_0_343, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_340]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_344, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_284, c_0_341]), c_0_288])).
% 0.65/0.81  cnf(c_0_345, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_342]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_346, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_343])).
% 0.65/0.81  cnf(c_0_347, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_344]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_348, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_345])).
% 0.65/0.81  cnf(c_0_349, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_346, c_0_191])).
% 0.65/0.81  cnf(c_0_350, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_71, c_0_338])).
% 0.65/0.81  cnf(c_0_351, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_347, c_0_15]), c_0_16]), c_0_18])]), c_0_21])).
% 0.65/0.81  cnf(c_0_352, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_348, c_0_182])).
% 0.65/0.81  cnf(c_0_353, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_292, c_0_349]), c_0_296])).
% 0.65/0.81  cnf(c_0_354, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_350]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_355, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_351, c_0_352])).
% 0.65/0.81  cnf(c_0_356, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_353]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_357, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_74, c_0_354])).
% 0.65/0.81  cnf(c_0_358, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|~r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_93, c_0_333])).
% 0.65/0.81  cnf(c_0_359, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_355, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_360, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_356, c_0_15]), c_0_16]), c_0_18])]), c_0_21])).
% 0.65/0.81  cnf(c_0_361, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_357, c_0_191])).
% 0.65/0.81  cnf(c_0_362, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_358, c_0_359])).
% 0.65/0.81  cnf(c_0_363, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_360, c_0_361])).
% 0.65/0.81  cnf(c_0_364, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_344]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_365, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_362]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_366, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|~r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_93, c_0_338])).
% 0.65/0.81  cnf(c_0_367, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_363, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_368, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_364, c_0_15]), c_0_16]), c_0_18])]), c_0_21])).
% 0.65/0.81  cnf(c_0_369, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_365]), c_0_182])).
% 0.65/0.81  cnf(c_0_370, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_366, c_0_367])).
% 0.65/0.81  cnf(c_0_371, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_368, c_0_352])).
% 0.65/0.81  cnf(c_0_372, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_284, c_0_369]), c_0_288])).
% 0.65/0.81  cnf(c_0_373, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_353]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_374, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r2_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_370]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_375, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_371, c_0_96]), c_0_95])])).
% 0.65/0.81  cnf(c_0_376, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_53, c_0_372])).
% 0.65/0.81  cnf(c_0_377, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_373, c_0_15]), c_0_16]), c_0_18])]), c_0_21])).
% 0.65/0.81  cnf(c_0_378, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_374]), c_0_191])).
% 0.65/0.81  cnf(c_0_379, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_375, c_0_376])).
% 0.65/0.81  cnf(c_0_380, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_377, c_0_361])).
% 0.65/0.81  cnf(c_0_381, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_292, c_0_378]), c_0_296])).
% 0.65/0.81  cnf(c_0_382, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_358, c_0_379])).
% 0.65/0.81  cnf(c_0_383, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_380, c_0_96]), c_0_95])])).
% 0.65/0.81  cnf(c_0_384, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_53, c_0_381])).
% 0.65/0.81  cnf(c_0_385, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))|r2_waybel_9(esk9_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_382]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_386, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_383, c_0_384])).
% 0.65/0.81  cnf(c_0_387, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk7_2(esk9_0,esk10_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_385]), c_0_182])).
% 0.65/0.81  cnf(c_0_388, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_366, c_0_386])).
% 0.65/0.81  cnf(c_0_389, plain, (r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|esk6_2(X1,X2)!=esk7_2(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.65/0.81  cnf(c_0_390, negated_conjecture, (esk7_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_284, c_0_387]), c_0_288])).
% 0.65/0.81  cnf(c_0_391, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))|r2_waybel_9(esk9_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_388]), c_0_15]), c_0_33])])).
% 0.65/0.81  cnf(c_0_392, negated_conjecture, (r2_hidden(X1,k10_yellow_6(esk9_0,esk10_0))|esk6_2(esk9_0,esk10_0)!=k1_waybel_9(esk9_0,esk10_0)|~r3_waybel_9(esk9_0,esk10_0,X1)|~l1_pre_topc(esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_389, c_0_390]), c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_15])]), c_0_21]), c_0_43])).
% 0.65/0.81  cnf(c_0_393, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)|r3_waybel_9(esk9_0,esk10_0,esk6_2(esk9_0,esk10_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_391]), c_0_191])).
% 0.65/0.81  cnf(c_0_394, negated_conjecture, (r2_hidden(X1,k10_yellow_6(esk9_0,esk10_0))|esk6_2(esk9_0,esk10_0)!=k1_waybel_9(esk9_0,esk10_0)|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_392, c_0_26]), c_0_27])])).
% 0.65/0.81  cnf(c_0_395, negated_conjecture, (esk6_2(esk9_0,esk10_0)=k1_waybel_9(esk9_0,esk10_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_292, c_0_393]), c_0_296])).
% 0.65/0.81  cnf(c_0_396, negated_conjecture, (r2_hidden(X1,k10_yellow_6(esk9_0,esk10_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_394, c_0_395])])).
% 0.65/0.81  cnf(c_0_397, negated_conjecture, (r2_hidden(k1_waybel_9(esk9_0,esk10_0),k10_yellow_6(esk9_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_396, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_398, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_397])])).
% 0.65/0.81  cnf(c_0_399, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_398]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_400, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_397])])).
% 0.65/0.81  cnf(c_0_401, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_399, c_0_15]), c_0_16]), c_0_18])]), c_0_21]), c_0_400])).
% 0.65/0.81  cnf(c_0_402, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_401, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_403, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_398]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_404, negated_conjecture, (m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_402])).
% 0.65/0.81  cnf(c_0_405, negated_conjecture, (~r2_waybel_9(esk9_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_397])])).
% 0.65/0.81  cnf(c_0_406, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_403, c_0_15]), c_0_16]), c_0_18])]), c_0_21]), c_0_400])).
% 0.65/0.81  cnf(c_0_407, negated_conjecture, (m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_404]), c_0_15]), c_0_33])]), c_0_405])).
% 0.65/0.81  cnf(c_0_408, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_406, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_409, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_407])).
% 0.65/0.81  cnf(c_0_410, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_408, c_0_409])).
% 0.65/0.81  cnf(c_0_411, negated_conjecture, (m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_99, c_0_410])).
% 0.65/0.81  cnf(c_0_412, negated_conjecture, (m1_subset_1(esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_411]), c_0_15]), c_0_33])]), c_0_405])).
% 0.65/0.81  cnf(c_0_413, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk3_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_53, c_0_412])).
% 0.65/0.81  cnf(c_0_414, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_413])])).
% 0.65/0.81  cnf(c_0_415, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_64, c_0_414])).
% 0.65/0.81  cnf(c_0_416, negated_conjecture, (m1_subset_1(esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_415]), c_0_15]), c_0_33])]), c_0_405])).
% 0.65/0.81  cnf(c_0_417, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_71, c_0_414])).
% 0.65/0.81  cnf(c_0_418, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk4_4(esk9_0,X2,X1,X1),u1_struct_0(esk9_0))|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_416]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_419, negated_conjecture, (r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_417]), c_0_15]), c_0_33])]), c_0_405])).
% 0.65/0.81  cnf(c_0_420, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|m1_subset_1(esk4_4(esk9_0,esk10_0,X1,X1),u1_struct_0(esk9_0))|~r3_waybel_9(esk9_0,esk10_0,X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_418, c_0_15]), c_0_16]), c_0_18]), c_0_419])]), c_0_21])).
% 0.65/0.81  cnf(c_0_421, negated_conjecture, (r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))|~r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_93, c_0_414])).
% 0.65/0.81  cnf(c_0_422, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_420, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_423, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|v2_struct_0(X2)|~r3_waybel_9(esk9_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,X2,X1,X1)),esk9_0,esk9_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk9_0)|~r1_lattice3(esk9_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,X2)),esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_416]), c_0_17]), c_0_38]), c_0_39]), c_0_40]), c_0_19]), c_0_20]), c_0_27]), c_0_41]), c_0_24])])).
% 0.65/0.81  cnf(c_0_424, negated_conjecture, (m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))|r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_421, c_0_422])).
% 0.65/0.81  cnf(c_0_425, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),X1)|~r3_waybel_9(esk9_0,esk10_0,X1)|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,X1,X1)),esk9_0,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_423, c_0_15]), c_0_16]), c_0_18]), c_0_419])]), c_0_21])).
% 0.65/0.81  cnf(c_0_426, negated_conjecture, (m1_subset_1(esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0)),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_424]), c_0_15]), c_0_33])]), c_0_405])).
% 0.65/0.81  cnf(c_0_427, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))|~v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_425, c_0_95]), c_0_96])])).
% 0.65/0.81  cnf(c_0_428, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk9_0,esk4_4(esk9_0,esk10_0,k1_waybel_9(esk9_0,esk10_0),k1_waybel_9(esk9_0,esk10_0))),esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_53, c_0_426])).
% 0.65/0.81  cnf(c_0_429, negated_conjecture, (r1_orders_2(esk9_0,esk2_3(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0)),k1_waybel_9(esk9_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_427, c_0_428])])).
% 0.65/0.81  cnf(c_0_430, negated_conjecture, (r2_yellow_0(esk9_0,k2_relset_1(u1_struct_0(esk10_0),u1_struct_0(esk9_0),u1_waybel_0(esk9_0,esk10_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_421, c_0_429])])).
% 0.65/0.81  cnf(c_0_431, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_430]), c_0_15]), c_0_33])]), c_0_405]), ['proof']).
% 0.65/0.81  # SZS output end CNFRefutation
% 0.65/0.81  # Proof object total steps             : 432
% 0.65/0.81  # Proof object clause steps            : 411
% 0.65/0.81  # Proof object formula steps           : 21
% 0.65/0.81  # Proof object conjectures             : 390
% 0.65/0.81  # Proof object clause conjectures      : 387
% 0.65/0.81  # Proof object formula conjectures     : 3
% 0.65/0.81  # Proof object initial clauses used    : 36
% 0.65/0.81  # Proof object initial formulas used   : 10
% 0.65/0.81  # Proof object generating inferences   : 353
% 0.65/0.81  # Proof object simplifying inferences  : 899
% 0.65/0.81  # Training examples: 0 positive, 0 negative
% 0.65/0.81  # Parsed axioms                        : 10
% 0.65/0.81  # Removed by relevancy pruning/SinE    : 0
% 0.65/0.81  # Initial clauses                      : 40
% 0.65/0.81  # Removed in clause preprocessing      : 0
% 0.65/0.81  # Initial clauses in saturation        : 40
% 0.65/0.81  # Processed clauses                    : 1787
% 0.65/0.81  # ...of these trivial                  : 2
% 0.65/0.81  # ...subsumed                          : 272
% 0.65/0.81  # ...remaining for further processing  : 1513
% 0.65/0.81  # Other redundant clauses eliminated   : 4
% 0.65/0.81  # Clauses deleted for lack of memory   : 0
% 0.65/0.81  # Backward-subsumed                    : 822
% 0.65/0.81  # Backward-rewritten                   : 502
% 0.65/0.81  # Generated clauses                    : 3606
% 0.65/0.81  # ...of the previous two non-trivial   : 3520
% 0.65/0.81  # Contextual simplify-reflections      : 125
% 0.65/0.81  # Paramodulations                      : 3599
% 0.65/0.81  # Factorizations                       : 0
% 0.65/0.81  # Equation resolutions                 : 4
% 0.65/0.81  # Propositional unsat checks           : 0
% 0.65/0.81  #    Propositional check models        : 0
% 0.65/0.81  #    Propositional check unsatisfiable : 0
% 0.65/0.81  #    Propositional clauses             : 0
% 0.65/0.81  #    Propositional clauses after purity: 0
% 0.65/0.81  #    Propositional unsat core size     : 0
% 0.65/0.81  #    Propositional preprocessing time  : 0.000
% 0.65/0.81  #    Propositional encoding time       : 0.000
% 0.65/0.81  #    Propositional solver time         : 0.000
% 0.65/0.81  #    Success case prop preproc time    : 0.000
% 0.65/0.81  #    Success case prop encoding time   : 0.000
% 0.65/0.81  #    Success case prop solver time     : 0.000
% 0.65/0.81  # Current number of processed clauses  : 142
% 0.65/0.81  #    Positive orientable unit clauses  : 37
% 0.65/0.81  #    Positive unorientable unit clauses: 0
% 0.65/0.81  #    Negative unit clauses             : 3
% 0.65/0.81  #    Non-unit-clauses                  : 102
% 0.65/0.81  # Current number of unprocessed clauses: 45
% 0.65/0.81  # ...number of literals in the above   : 227
% 0.65/0.81  # Current number of archived formulas  : 0
% 0.65/0.81  # Current number of archived clauses   : 1367
% 0.65/0.81  # Clause-clause subsumption calls (NU) : 196021
% 0.65/0.81  # Rec. Clause-clause subsumption calls : 11702
% 0.65/0.81  # Non-unit clause-clause subsumptions  : 1218
% 0.65/0.81  # Unit Clause-clause subsumption calls : 1021
% 0.65/0.81  # Rewrite failures with RHS unbound    : 0
% 0.65/0.81  # BW rewrite match attempts            : 58
% 0.65/0.81  # BW rewrite match successes           : 20
% 0.65/0.81  # Condensation attempts                : 0
% 0.65/0.81  # Condensation successes               : 0
% 0.65/0.81  # Termbank termtop insertions          : 260367
% 0.65/0.82  
% 0.65/0.82  # -------------------------------------------------
% 0.65/0.82  # User time                : 0.465 s
% 0.65/0.82  # System time              : 0.011 s
% 0.65/0.82  # Total time               : 0.476 s
% 0.65/0.82  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
