%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:48 EST 2020

% Result     : Theorem 0.66s
% Output     : CNFRefutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  432 (17272572034 expanded)
%              Number of clauses        :  411 (5533176145 expanded)
%              Number of leaves         :   10 (4218514327 expanded)
%              Depth                    :  145
%              Number of atoms          : 2206 (205581671763 expanded)
%              Number of equality atoms :  238 (605809022 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_waybel_9)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(dt_l1_waybel_9,axiom,(
    ! [X1] :
      ( l1_waybel_9(X1)
     => ( l1_pre_topc(X1)
        & l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_waybel_9)).

fof(t31_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) )
               => ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) ) )
              & ( ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) )
               => ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_yellow_0)).

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

fof(d4_waybel_9,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ( r2_waybel_9(X1,X2)
          <=> r2_yellow_0(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l52_waybel_9)).

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
    ! [X6] :
      ( ~ l1_orders_2(X6)
      | ~ v1_lattice3(X6)
      | ~ v2_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

fof(c_0_12,negated_conjecture,(
    ! [X40] :
      ( v2_pre_topc(esk8_0)
      & v8_pre_topc(esk8_0)
      & v3_orders_2(esk8_0)
      & v4_orders_2(esk8_0)
      & v5_orders_2(esk8_0)
      & v1_lattice3(esk8_0)
      & v2_lattice3(esk8_0)
      & v1_compts_1(esk8_0)
      & l1_waybel_9(esk8_0)
      & ( ~ m1_subset_1(X40,u1_struct_0(esk8_0))
        | v5_pre_topc(k4_waybel_1(esk8_0,X40),esk8_0,esk8_0) )
      & ~ v2_struct_0(esk9_0)
      & v4_orders_2(esk9_0)
      & v7_waybel_0(esk9_0)
      & l1_waybel_0(esk9_0,esk8_0)
      & v11_waybel_0(esk9_0,esk8_0)
      & ( ~ r2_waybel_9(esk8_0,esk9_0)
        | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).

fof(c_0_13,plain,(
    ! [X15] :
      ( ( l1_pre_topc(X15)
        | ~ l1_waybel_9(X15) )
      & ( l1_orders_2(X15)
        | ~ l1_waybel_9(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).

cnf(c_0_14,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_lattice3(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( l1_orders_2(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( l1_waybel_9(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X27,X28] :
      ( ( m1_subset_1(esk4_2(X27,X28),u1_struct_0(X27))
        | v2_struct_0(X28)
        | ~ v4_orders_2(X28)
        | ~ v7_waybel_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ v8_pre_topc(X27)
        | ~ v1_compts_1(X27)
        | ~ l1_pre_topc(X27) )
      & ( r3_waybel_9(X27,X28,esk4_2(X27,X28))
        | v2_struct_0(X28)
        | ~ v4_orders_2(X28)
        | ~ v7_waybel_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ v8_pre_topc(X27)
        | ~ v1_compts_1(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_waybel_9])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    | ~ l1_orders_2(esk8_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk8_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( l1_waybel_0(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( v7_waybel_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( v1_compts_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( v4_orders_2(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( v8_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])])).

fof(c_0_30,plain,(
    ! [X35,X36,X37] :
      ( ( m1_subset_1(esk7_3(X35,X36,X37),u1_struct_0(X35))
        | ~ v11_waybel_0(X37,X35)
        | ~ r3_waybel_9(X35,X37,X36)
        | X36 = k1_waybel_9(X35,X37)
        | v2_struct_0(X37)
        | ~ v4_orders_2(X37)
        | ~ v7_waybel_0(X37)
        | ~ l1_waybel_0(X37,X35)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ v2_pre_topc(X35)
        | ~ v8_pre_topc(X35)
        | ~ v3_orders_2(X35)
        | ~ v4_orders_2(X35)
        | ~ v5_orders_2(X35)
        | ~ v1_lattice3(X35)
        | ~ v2_lattice3(X35)
        | ~ v1_compts_1(X35)
        | ~ l1_waybel_9(X35) )
      & ( ~ v5_pre_topc(k4_waybel_1(X35,esk7_3(X35,X36,X37)),X35,X35)
        | ~ v11_waybel_0(X37,X35)
        | ~ r3_waybel_9(X35,X37,X36)
        | X36 = k1_waybel_9(X35,X37)
        | v2_struct_0(X37)
        | ~ v4_orders_2(X37)
        | ~ v7_waybel_0(X37)
        | ~ l1_waybel_0(X37,X35)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ v2_pre_topc(X35)
        | ~ v8_pre_topc(X35)
        | ~ v3_orders_2(X35)
        | ~ v4_orders_2(X35)
        | ~ v5_orders_2(X35)
        | ~ v1_lattice3(X35)
        | ~ v2_lattice3(X35)
        | ~ v1_compts_1(X35)
        | ~ l1_waybel_9(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_waybel_9])])])])])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ l1_pre_topc(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])]),c_0_28]),c_0_29])).

cnf(c_0_32,plain,
    ( l1_pre_topc(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
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
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk4_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_17])])).

cnf(c_0_36,negated_conjecture,
    ( v2_lattice3(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( v4_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( v3_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( v5_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( r3_waybel_9(esk8_0,esk9_0,esk4_2(esk8_0,esk9_0))
    | ~ l1_pre_topc(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])]),c_0_28]),c_0_29])).

cnf(c_0_41,plain,
    ( X2 = k1_waybel_9(X1,X3)
    | v2_struct_0(X3)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk7_3(X1,X2,X3)),X1,X1)
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
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( esk4_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,X1)
    | m1_subset_1(esk7_3(esk8_0,esk4_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))
    | ~ v11_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_43,negated_conjecture,
    ( v11_waybel_0(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,negated_conjecture,
    ( r3_waybel_9(esk8_0,esk9_0,esk4_2(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_32]),c_0_17])])).

cnf(c_0_45,negated_conjecture,
    ( esk4_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))
    | ~ v11_waybel_0(X1,esk8_0)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk4_2(esk8_0,esk9_0),X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_35]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

fof(c_0_46,plain,(
    ! [X16,X17,X18,X19] :
      ( ( m1_subset_1(esk2_4(X16,X17,X18,X19),u1_struct_0(X16))
        | X18 != X19
        | ~ v11_waybel_0(X17,X16)
        | ~ r3_waybel_9(X16,X17,X18)
        | r1_lattice3(X16,k2_relset_1(u1_struct_0(X17),u1_struct_0(X16),u1_waybel_0(X16,X17)),X19)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | v2_struct_0(X17)
        | ~ v4_orders_2(X17)
        | ~ v7_waybel_0(X17)
        | ~ l1_waybel_0(X17,X16)
        | ~ v2_pre_topc(X16)
        | ~ v8_pre_topc(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ v1_lattice3(X16)
        | ~ v2_lattice3(X16)
        | ~ v1_compts_1(X16)
        | ~ l1_waybel_9(X16) )
      & ( ~ v5_pre_topc(k4_waybel_1(X16,esk2_4(X16,X17,X18,X19)),X16,X16)
        | X18 != X19
        | ~ v11_waybel_0(X17,X16)
        | ~ r3_waybel_9(X16,X17,X18)
        | r1_lattice3(X16,k2_relset_1(u1_struct_0(X17),u1_struct_0(X16),u1_waybel_0(X16,X17)),X19)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | v2_struct_0(X17)
        | ~ v4_orders_2(X17)
        | ~ v7_waybel_0(X17)
        | ~ l1_waybel_0(X17,X16)
        | ~ v2_pre_topc(X16)
        | ~ v8_pre_topc(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ v1_lattice3(X16)
        | ~ v2_lattice3(X16)
        | ~ v1_compts_1(X16)
        | ~ l1_waybel_9(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l51_waybel_9])])])])])])).

cnf(c_0_47,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,X1),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_48,negated_conjecture,
    ( esk4_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk4_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_23]),c_0_25]),c_0_22])]),c_0_28])).

cnf(c_0_49,negated_conjecture,
    ( esk4_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk4_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_43]),c_0_44]),c_0_23]),c_0_25]),c_0_22])]),c_0_28])).

fof(c_0_50,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( r1_lattice3(X7,X9,X8)
        | X8 != k2_yellow_0(X7,X9)
        | ~ r2_yellow_0(X7,X9)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_lattice3(X7,X9,X10)
        | r1_orders_2(X7,X10,X8)
        | X8 != k2_yellow_0(X7,X9)
        | ~ r2_yellow_0(X7,X9)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( X8 = k2_yellow_0(X7,X11)
        | m1_subset_1(esk1_3(X7,X8,X11),u1_struct_0(X7))
        | ~ r1_lattice3(X7,X11,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r2_yellow_0(X7,X11)
        | m1_subset_1(esk1_3(X7,X8,X11),u1_struct_0(X7))
        | ~ r1_lattice3(X7,X11,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( X8 = k2_yellow_0(X7,X11)
        | r1_lattice3(X7,X11,esk1_3(X7,X8,X11))
        | ~ r1_lattice3(X7,X11,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r2_yellow_0(X7,X11)
        | r1_lattice3(X7,X11,esk1_3(X7,X8,X11))
        | ~ r1_lattice3(X7,X11,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( X8 = k2_yellow_0(X7,X11)
        | ~ r1_orders_2(X7,esk1_3(X7,X8,X11),X8)
        | ~ r1_lattice3(X7,X11,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r2_yellow_0(X7,X11)
        | ~ r1_orders_2(X7,esk1_3(X7,X8,X11),X8)
        | ~ r1_lattice3(X7,X11,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_yellow_0])])])])])])).

cnf(c_0_51,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X1))
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
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( esk4_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_53,plain,
    ( r2_yellow_0(X1,X2)
    | m1_subset_1(esk1_3(X1,X3,X2),u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,plain,
    ( r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)
    | m1_subset_1(esk2_4(X1,X2,X3,X3),u1_struct_0(X1))
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
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k1_waybel_9(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_52])).

fof(c_0_56,plain,(
    ! [X30,X31,X34] :
      ( ( m1_subset_1(esk5_2(X30,X31),u1_struct_0(X30))
        | ~ m1_subset_1(X34,u1_struct_0(X30))
        | ~ r3_waybel_9(X30,X31,X34)
        | r2_hidden(X34,k10_yellow_6(X30,X31))
        | v2_struct_0(X31)
        | ~ v4_orders_2(X31)
        | ~ v7_waybel_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ v8_pre_topc(X30)
        | ~ v1_compts_1(X30)
        | ~ l1_pre_topc(X30) )
      & ( m1_subset_1(esk6_2(X30,X31),u1_struct_0(X30))
        | ~ m1_subset_1(X34,u1_struct_0(X30))
        | ~ r3_waybel_9(X30,X31,X34)
        | r2_hidden(X34,k10_yellow_6(X30,X31))
        | v2_struct_0(X31)
        | ~ v4_orders_2(X31)
        | ~ v7_waybel_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ v8_pre_topc(X30)
        | ~ v1_compts_1(X30)
        | ~ l1_pre_topc(X30) )
      & ( r3_waybel_9(X30,X31,esk5_2(X30,X31))
        | ~ m1_subset_1(X34,u1_struct_0(X30))
        | ~ r3_waybel_9(X30,X31,X34)
        | r2_hidden(X34,k10_yellow_6(X30,X31))
        | v2_struct_0(X31)
        | ~ v4_orders_2(X31)
        | ~ v7_waybel_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ v8_pre_topc(X30)
        | ~ v1_compts_1(X30)
        | ~ l1_pre_topc(X30) )
      & ( r3_waybel_9(X30,X31,esk6_2(X30,X31))
        | ~ m1_subset_1(X34,u1_struct_0(X30))
        | ~ r3_waybel_9(X30,X31,X34)
        | r2_hidden(X34,k10_yellow_6(X30,X31))
        | v2_struct_0(X31)
        | ~ v4_orders_2(X31)
        | ~ v7_waybel_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ v8_pre_topc(X30)
        | ~ v1_compts_1(X30)
        | ~ l1_pre_topc(X30) )
      & ( esk5_2(X30,X31) != esk6_2(X30,X31)
        | ~ m1_subset_1(X34,u1_struct_0(X30))
        | ~ r3_waybel_9(X30,X31,X34)
        | r2_hidden(X34,k10_yellow_6(X30,X31))
        | v2_struct_0(X31)
        | ~ v4_orders_2(X31)
        | ~ v7_waybel_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ v8_pre_topc(X30)
        | ~ v1_compts_1(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t33_waybel_9])])])])])])).

cnf(c_0_57,negated_conjecture,
    ( r2_yellow_0(esk8_0,X1)
    | m1_subset_1(esk1_3(esk8_0,esk4_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))
    | ~ r1_lattice3(esk8_0,X1,esk4_2(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_35]),c_0_39]),c_0_20])])).

cnf(c_0_58,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X1)),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0))
    | ~ v11_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_59,negated_conjecture,
    ( r3_waybel_9(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_52])).

cnf(c_0_60,plain,
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

cnf(c_0_61,plain,
    ( r2_yellow_0(X1,X2)
    | r1_lattice3(X1,X2,esk1_3(X1,X3,X2))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_62,plain,(
    ! [X13,X14] :
      ( ( ~ r2_waybel_9(X13,X14)
        | r2_yellow_0(X13,k2_relset_1(u1_struct_0(X14),u1_struct_0(X13),u1_waybel_0(X13,X14)))
        | ~ l1_waybel_0(X14,X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r2_yellow_0(X13,k2_relset_1(u1_struct_0(X14),u1_struct_0(X13),u1_waybel_0(X13,X14)))
        | r2_waybel_9(X13,X14)
        | ~ l1_waybel_0(X14,X13)
        | ~ l1_orders_2(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_waybel_9])])])])).

cnf(c_0_63,negated_conjecture,
    ( r2_yellow_0(esk8_0,X1)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))
    | ~ r1_lattice3(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_52]),c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_43]),c_0_59]),c_0_23]),c_0_25]),c_0_22])]),c_0_28])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))
    | m1_subset_1(esk6_2(esk8_0,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(esk8_0)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_35]),c_0_24]),c_0_26]),c_0_27])]),c_0_29])).

cnf(c_0_66,negated_conjecture,
    ( r1_lattice3(esk8_0,X1,esk1_3(esk8_0,esk4_2(esk8_0,esk9_0),X1))
    | r2_yellow_0(esk8_0,X1)
    | ~ r1_lattice3(esk8_0,X1,esk4_2(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_35]),c_0_39]),c_0_20])])).

cnf(c_0_67,plain,
    ( r2_waybel_9(X1,X2)
    | ~ r2_yellow_0(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))
    | m1_subset_1(esk6_2(esk8_0,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_32]),c_0_17])])).

cnf(c_0_70,negated_conjecture,
    ( r1_lattice3(esk8_0,X1,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),X1))
    | r2_yellow_0(esk8_0,X1)
    | ~ r1_lattice3(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_52]),c_0_52])).

cnf(c_0_71,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_72,plain,(
    ! [X21,X22,X23,X24,X26] :
      ( ( m1_subset_1(esk3_4(X21,X22,X23,X24),u1_struct_0(X21))
        | X23 != X24
        | ~ r3_waybel_9(X21,X22,X23)
        | ~ m1_subset_1(X26,u1_struct_0(X21))
        | ~ r1_lattice3(X21,k2_relset_1(u1_struct_0(X22),u1_struct_0(X21),u1_waybel_0(X21,X22)),X26)
        | r1_orders_2(X21,X26,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | ~ v2_pre_topc(X21)
        | ~ v8_pre_topc(X21)
        | ~ v3_orders_2(X21)
        | ~ v4_orders_2(X21)
        | ~ v5_orders_2(X21)
        | ~ v1_lattice3(X21)
        | ~ v2_lattice3(X21)
        | ~ v1_compts_1(X21)
        | ~ l1_waybel_9(X21) )
      & ( ~ v5_pre_topc(k4_waybel_1(X21,esk3_4(X21,X22,X23,X24)),X21,X21)
        | X23 != X24
        | ~ r3_waybel_9(X21,X22,X23)
        | ~ m1_subset_1(X26,u1_struct_0(X21))
        | ~ r1_lattice3(X21,k2_relset_1(u1_struct_0(X22),u1_struct_0(X21),u1_waybel_0(X21,X22)),X26)
        | r1_orders_2(X21,X26,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | ~ v2_pre_topc(X21)
        | ~ v8_pre_topc(X21)
        | ~ v3_orders_2(X21)
        | ~ v4_orders_2(X21)
        | ~ v5_orders_2(X21)
        | ~ v1_lattice3(X21)
        | ~ v2_lattice3(X21)
        | ~ v1_compts_1(X21)
        | ~ l1_waybel_9(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l52_waybel_9])])])])])])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_waybel_9(esk8_0,esk9_0)
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_74,negated_conjecture,
    ( r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_22]),c_0_20])])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_22]),c_0_44]),c_0_23]),c_0_25])]),c_0_28])).

cnf(c_0_76,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_64])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))
    | m1_subset_1(esk5_2(esk8_0,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(esk8_0)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_35]),c_0_24]),c_0_26]),c_0_27])]),c_0_29])).

cnf(c_0_78,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X1))
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
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_75,c_0_52])).

cnf(c_0_81,negated_conjecture,
    ( r2_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_76]),c_0_22]),c_0_20])])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))
    | m1_subset_1(esk5_2(esk8_0,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_32]),c_0_17])])).

cnf(c_0_83,plain,
    ( r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk1_3(X1,X3,X2),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_84,plain,
    ( r1_orders_2(X1,X2,X3)
    | m1_subset_1(esk3_4(X1,X4,X3,X3),u1_struct_0(X1))
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
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_22]),c_0_44]),c_0_23]),c_0_25])]),c_0_28])).

cnf(c_0_88,negated_conjecture,
    ( r2_yellow_0(esk8_0,X1)
    | ~ r1_orders_2(esk8_0,esk1_3(esk8_0,esk4_2(esk8_0,esk9_0),X1),esk4_2(esk8_0,esk9_0))
    | ~ r1_lattice3(esk8_0,X1,esk4_2(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_35]),c_0_39]),c_0_20])])).

cnf(c_0_89,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_90,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_80])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_87,c_0_52])).

cnf(c_0_92,negated_conjecture,
    ( r2_yellow_0(esk8_0,X1)
    | ~ r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),X1),k1_waybel_9(esk8_0,esk9_0))
    | ~ r1_lattice3(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_52]),c_0_52]),c_0_52])).

cnf(c_0_93,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_91])).

cnf(c_0_95,plain,
    ( r1_orders_2(X1,X5,X4)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X2,X3,X4)),X1,X1)
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
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_96,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_64])).

cnf(c_0_97,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_59]),c_0_55])])).

cnf(c_0_98,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_94]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_99,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_91])).

cnf(c_0_100,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X4)
    | ~ r3_waybel_9(X1,X4,X3)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X4,X3,X3)),X1,X1)
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
    inference(er,[status(thm)],[c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_85]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_104,negated_conjecture,
    ( r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_101]),c_0_22]),c_0_20])])).

cnf(c_0_105,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_59]),c_0_55])])).

cnf(c_0_106,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_90])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_104]),c_0_80])).

cnf(c_0_108,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_59]),c_0_55])])).

cnf(c_0_110,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_107])).

cnf(c_0_111,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_94]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_112,negated_conjecture,
    ( r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_108]),c_0_22]),c_0_20])])).

cnf(c_0_113,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_99])).

cnf(c_0_115,negated_conjecture,
    ( m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_112]),c_0_91])).

cnf(c_0_116,plain,
    ( r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk2_4(X1,X2,X3,X4)),X1,X1)
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
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_117,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_113])).

cnf(c_0_118,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_59]),c_0_55])])).

cnf(c_0_119,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_115])).

cnf(c_0_120,plain,
    ( r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ v11_waybel_0(X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk2_4(X1,X2,X3,X3)),X1,X1)
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
    inference(er,[status(thm)],[c_0_116])).

cnf(c_0_121,negated_conjecture,
    ( r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_117]),c_0_22]),c_0_20])])).

cnf(c_0_122,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_123,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X1)),k1_waybel_9(esk8_0,esk9_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0))
    | ~ v11_waybel_0(X1,esk8_0)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_55]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_124,negated_conjecture,
    ( m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_121]),c_0_80])).

cnf(c_0_125,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_122])).

cnf(c_0_126,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_43]),c_0_59]),c_0_23]),c_0_25]),c_0_22])]),c_0_28])).

cnf(c_0_127,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_124])).

cnf(c_0_128,negated_conjecture,
    ( r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_125]),c_0_22]),c_0_20])])).

cnf(c_0_129,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_130,negated_conjecture,
    ( m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_128]),c_0_91])).

cnf(c_0_131,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_129])).

cnf(c_0_132,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_130])).

cnf(c_0_133,negated_conjecture,
    ( r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_131]),c_0_22]),c_0_20])])).

cnf(c_0_134,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_129])).

cnf(c_0_135,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_132])).

cnf(c_0_136,negated_conjecture,
    ( m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_133]),c_0_80])).

cnf(c_0_137,negated_conjecture,
    ( r2_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_134]),c_0_22]),c_0_20])])).

cnf(c_0_138,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_135])).

cnf(c_0_139,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_136]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_140,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_137]),c_0_80])).

cnf(c_0_141,negated_conjecture,
    ( r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_138]),c_0_22]),c_0_20])])).

cnf(c_0_142,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_135])).

cnf(c_0_143,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_140])).

cnf(c_0_144,negated_conjecture,
    ( m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_141]),c_0_91])).

cnf(c_0_145,negated_conjecture,
    ( r2_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_142]),c_0_22]),c_0_20])])).

cnf(c_0_146,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_129])).

cnf(c_0_147,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_59]),c_0_55])])).

cnf(c_0_148,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_144]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_149,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_145]),c_0_91])).

cnf(c_0_150,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_151,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_149])).

cnf(c_0_152,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_136]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_153,negated_conjecture,
    ( r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_150]),c_0_22]),c_0_20])])).

cnf(c_0_154,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_135])).

cnf(c_0_155,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_59]),c_0_55])])).

cnf(c_0_156,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_140])).

cnf(c_0_157,negated_conjecture,
    ( m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_153]),c_0_80])).

cnf(c_0_158,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_154,c_0_155])).

cnf(c_0_159,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_59]),c_0_55])])).

cnf(c_0_160,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_157])).

cnf(c_0_161,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_144]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_162,negated_conjecture,
    ( r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_158]),c_0_22]),c_0_20])])).

cnf(c_0_163,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_159,c_0_160])).

cnf(c_0_164,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_149])).

cnf(c_0_165,negated_conjecture,
    ( m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_162]),c_0_91])).

cnf(c_0_166,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_146,c_0_163])).

cnf(c_0_167,plain,
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

cnf(c_0_168,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_59]),c_0_55])])).

cnf(c_0_169,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_165])).

cnf(c_0_170,negated_conjecture,
    ( r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_166]),c_0_22]),c_0_20])])).

cnf(c_0_171,negated_conjecture,
    ( r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))
    | r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,X1))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(esk8_0)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_55]),c_0_24]),c_0_26]),c_0_27])]),c_0_29])).

cnf(c_0_172,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_168,c_0_169])).

cnf(c_0_173,negated_conjecture,
    ( m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_170]),c_0_80])).

cnf(c_0_174,negated_conjecture,
    ( r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))
    | r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,X1))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_32]),c_0_17])])).

cnf(c_0_175,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_154,c_0_172])).

cnf(c_0_176,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_177,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,X1)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,esk9_0))
    | ~ v11_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_173]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_178,negated_conjecture,
    ( r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))
    | r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_22]),c_0_59]),c_0_23]),c_0_25])]),c_0_28])).

cnf(c_0_179,negated_conjecture,
    ( r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_175]),c_0_22]),c_0_20])])).

cnf(c_0_180,negated_conjecture,
    ( r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))
    | r3_waybel_9(esk8_0,X1,esk5_2(esk8_0,X1))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(esk8_0)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_55]),c_0_24]),c_0_26]),c_0_27])]),c_0_29])).

cnf(c_0_181,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_43]),c_0_23]),c_0_25]),c_0_22])]),c_0_28])).

cnf(c_0_182,negated_conjecture,
    ( r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_178])).

cnf(c_0_183,negated_conjecture,
    ( m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_179]),c_0_91])).

cnf(c_0_184,negated_conjecture,
    ( r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))
    | r3_waybel_9(esk8_0,X1,esk5_2(esk8_0,X1))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_32]),c_0_17])])).

cnf(c_0_185,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_181,c_0_182])).

cnf(c_0_186,negated_conjecture,
    ( r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_178])).

cnf(c_0_187,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,X1)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk5_2(esk8_0,esk9_0))
    | ~ v11_waybel_0(X1,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_183]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_188,negated_conjecture,
    ( r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))
    | r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_22]),c_0_59]),c_0_23]),c_0_25])]),c_0_28])).

cnf(c_0_189,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_185]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_190,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_181,c_0_186])).

cnf(c_0_191,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187,c_0_43]),c_0_23]),c_0_25]),c_0_22])]),c_0_28])).

cnf(c_0_192,negated_conjecture,
    ( r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_188])).

cnf(c_0_193,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_190])).

cnf(c_0_194,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_191,c_0_192])).

cnf(c_0_195,negated_conjecture,
    ( r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_188])).

cnf(c_0_196,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193,c_0_59]),c_0_55])])).

cnf(c_0_197,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_194]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_198,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_191,c_0_195])).

cnf(c_0_199,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_196])).

cnf(c_0_200,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_198])).

cnf(c_0_201,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_199]),c_0_22]),c_0_20])])).

cnf(c_0_202,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_200,c_0_59]),c_0_55])])).

cnf(c_0_203,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_185]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_204,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_201])).

cnf(c_0_205,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_202])).

cnf(c_0_206,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_190])).

cnf(c_0_207,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_204,c_0_178]),c_0_181])).

cnf(c_0_208,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_205]),c_0_22]),c_0_20])])).

cnf(c_0_209,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_206,c_0_59]),c_0_55])])).

cnf(c_0_210,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_207])).

cnf(c_0_211,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_194]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_212,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_208])).

cnf(c_0_213,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_209,c_0_210])).

cnf(c_0_214,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_211,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_198])).

cnf(c_0_215,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_212,c_0_188]),c_0_191])).

cnf(c_0_216,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_213])).

cnf(c_0_217,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_214,c_0_59]),c_0_55])])).

cnf(c_0_218,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_215])).

cnf(c_0_219,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_216]),c_0_22]),c_0_20])])).

cnf(c_0_220,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_217,c_0_218])).

cnf(c_0_221,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_219])).

cnf(c_0_222,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_220])).

cnf(c_0_223,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_221,c_0_178]),c_0_181])).

cnf(c_0_224,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_222]),c_0_22]),c_0_20])])).

cnf(c_0_225,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_223])).

cnf(c_0_226,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_224])).

cnf(c_0_227,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_225])).

cnf(c_0_228,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_226,c_0_188]),c_0_191])).

cnf(c_0_229,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_227])).

cnf(c_0_230,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_228])).

cnf(c_0_231,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_229]),c_0_22]),c_0_20])])).

cnf(c_0_232,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_227])).

cnf(c_0_233,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_230])).

cnf(c_0_234,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_231])).

cnf(c_0_235,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_232]),c_0_22]),c_0_20])])).

cnf(c_0_236,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_233])).

cnf(c_0_237,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_234,c_0_178]),c_0_181])).

cnf(c_0_238,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_235])).

cnf(c_0_239,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_236]),c_0_22]),c_0_20])])).

cnf(c_0_240,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_233])).

cnf(c_0_241,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_237]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_242,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_238,c_0_178]),c_0_181])).

cnf(c_0_243,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_239])).

cnf(c_0_244,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_240]),c_0_22]),c_0_20])])).

cnf(c_0_245,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_241,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_242])).

cnf(c_0_246,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_188]),c_0_191])).

cnf(c_0_247,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_244])).

cnf(c_0_248,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_227])).

cnf(c_0_249,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_245,c_0_59]),c_0_55])])).

cnf(c_0_250,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_246]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_251,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_247,c_0_188]),c_0_191])).

cnf(c_0_252,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_248,c_0_249])).

cnf(c_0_253,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_250,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_251])).

cnf(c_0_254,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_252]),c_0_22]),c_0_20])])).

cnf(c_0_255,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_233])).

cnf(c_0_256,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_253,c_0_59]),c_0_55])])).

cnf(c_0_257,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_237]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_258,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_254])).

cnf(c_0_259,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_255,c_0_256])).

cnf(c_0_260,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_257,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_242])).

cnf(c_0_261,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_258,c_0_178]),c_0_181])).

cnf(c_0_262,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_259]),c_0_22]),c_0_20])])).

cnf(c_0_263,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_260,c_0_59]),c_0_55])])).

cnf(c_0_264,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_261])).

cnf(c_0_265,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_246]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_266,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_262])).

cnf(c_0_267,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_263,c_0_264])).

cnf(c_0_268,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_265,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_251])).

cnf(c_0_269,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_266,c_0_188]),c_0_191])).

cnf(c_0_270,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_248,c_0_267])).

cnf(c_0_271,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_268,c_0_59]),c_0_55])])).

cnf(c_0_272,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_269])).

cnf(c_0_273,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_270]),c_0_22]),c_0_20])])).

cnf(c_0_274,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_271,c_0_272])).

cnf(c_0_275,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,esk9_0))
    | ~ v11_waybel_0(X1,esk8_0)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_173]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_276,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_273])).

cnf(c_0_277,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_255,c_0_274])).

cnf(c_0_278,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | ~ r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_275,c_0_43]),c_0_23]),c_0_25]),c_0_22])]),c_0_28])).

cnf(c_0_279,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_276,c_0_178]),c_0_181])).

cnf(c_0_280,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_277]),c_0_22]),c_0_20])])).

cnf(c_0_281,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_278,c_0_182])).

cnf(c_0_282,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_279])).

cnf(c_0_283,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,X1)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk8_0,X1,esk5_2(esk8_0,esk9_0))
    | ~ v11_waybel_0(X1,esk8_0)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_183]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_284,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_280])).

cnf(c_0_285,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_281,c_0_282])).

cnf(c_0_286,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_278,c_0_186])).

cnf(c_0_287,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | ~ r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_283,c_0_43]),c_0_23]),c_0_25]),c_0_22])]),c_0_28])).

cnf(c_0_288,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_284,c_0_188]),c_0_191])).

cnf(c_0_289,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_285]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_290,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_286,c_0_282])).

cnf(c_0_291,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_287,c_0_192])).

cnf(c_0_292,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_288])).

cnf(c_0_293,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_289,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_290])).

cnf(c_0_294,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_291,c_0_292])).

cnf(c_0_295,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_287,c_0_195])).

cnf(c_0_296,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_293,c_0_59]),c_0_55])])).

cnf(c_0_297,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_294]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_298,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_295,c_0_292])).

cnf(c_0_299,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_296])).

cnf(c_0_300,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_297,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_298])).

cnf(c_0_301,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_299]),c_0_22]),c_0_20])])).

cnf(c_0_302,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_300,c_0_59]),c_0_55])])).

cnf(c_0_303,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_301])).

cnf(c_0_304,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_302])).

cnf(c_0_305,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_285]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_306,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_303,c_0_178])).

cnf(c_0_307,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_304]),c_0_22]),c_0_20])])).

cnf(c_0_308,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_305,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_290])).

cnf(c_0_309,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_278,c_0_306]),c_0_282])).

cnf(c_0_310,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_307])).

cnf(c_0_311,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_308,c_0_59]),c_0_55])])).

cnf(c_0_312,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_309])).

cnf(c_0_313,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_294]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_314,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_310,c_0_188])).

cnf(c_0_315,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_311,c_0_312])).

cnf(c_0_316,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_313,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_298])).

cnf(c_0_317,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_287,c_0_314]),c_0_292])).

cnf(c_0_318,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_315])).

cnf(c_0_319,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_59]),c_0_55])])).

cnf(c_0_320,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_317])).

cnf(c_0_321,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_318]),c_0_22]),c_0_20])])).

cnf(c_0_322,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_319,c_0_320])).

cnf(c_0_323,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_321])).

cnf(c_0_324,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_322])).

cnf(c_0_325,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_323,c_0_178])).

cnf(c_0_326,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_324]),c_0_22]),c_0_20])])).

cnf(c_0_327,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_278,c_0_325]),c_0_282])).

cnf(c_0_328,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_326])).

cnf(c_0_329,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_327])).

cnf(c_0_330,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_328,c_0_188])).

cnf(c_0_331,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_329])).

cnf(c_0_332,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_287,c_0_330]),c_0_292])).

cnf(c_0_333,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_331])).

cnf(c_0_334,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_332])).

cnf(c_0_335,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_333]),c_0_22]),c_0_20])])).

cnf(c_0_336,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_331])).

cnf(c_0_337,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_334])).

cnf(c_0_338,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_335])).

cnf(c_0_339,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_336]),c_0_22]),c_0_20])])).

cnf(c_0_340,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_337])).

cnf(c_0_341,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_338,c_0_178])).

cnf(c_0_342,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_339])).

cnf(c_0_343,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_340]),c_0_22]),c_0_20])])).

cnf(c_0_344,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_337])).

cnf(c_0_345,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_278,c_0_341]),c_0_282])).

cnf(c_0_346,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_342,c_0_178])).

cnf(c_0_347,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_343])).

cnf(c_0_348,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_344]),c_0_22]),c_0_20])])).

cnf(c_0_349,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_345]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_350,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_278,c_0_346]),c_0_282])).

cnf(c_0_351,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_347,c_0_188])).

cnf(c_0_352,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_348])).

cnf(c_0_353,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_349,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_350])).

cnf(c_0_354,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_287,c_0_351]),c_0_292])).

cnf(c_0_355,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_352,c_0_188])).

cnf(c_0_356,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | ~ r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_331])).

cnf(c_0_357,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_353,c_0_59]),c_0_55])])).

cnf(c_0_358,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_354]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_359,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_287,c_0_355]),c_0_292])).

cnf(c_0_360,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_356,c_0_357])).

cnf(c_0_361,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_358,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_359])).

cnf(c_0_362,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_360]),c_0_22]),c_0_20])])).

cnf(c_0_363,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | ~ r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_337])).

cnf(c_0_364,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_361,c_0_59]),c_0_55])])).

cnf(c_0_365,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_362])).

cnf(c_0_366,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_363,c_0_364])).

cnf(c_0_367,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_345]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_368,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_365,c_0_178])).

cnf(c_0_369,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_366]),c_0_22]),c_0_20])])).

cnf(c_0_370,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_367,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_350])).

cnf(c_0_371,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_278,c_0_368]),c_0_282])).

cnf(c_0_372,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_369])).

cnf(c_0_373,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_370,c_0_59]),c_0_55])])).

cnf(c_0_374,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_371])).

cnf(c_0_375,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_354]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_376,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_372,c_0_188])).

cnf(c_0_377,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_373,c_0_374])).

cnf(c_0_378,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_375,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_359])).

cnf(c_0_379,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_287,c_0_376]),c_0_292])).

cnf(c_0_380,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_356,c_0_377])).

cnf(c_0_381,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_378,c_0_59]),c_0_55])])).

cnf(c_0_382,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_379])).

cnf(c_0_383,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_380]),c_0_22]),c_0_20])])).

cnf(c_0_384,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_381,c_0_382])).

cnf(c_0_385,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_383])).

cnf(c_0_386,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_363,c_0_384])).

cnf(c_0_387,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_385,c_0_178])).

cnf(c_0_388,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r2_waybel_9(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_386]),c_0_22]),c_0_20])])).

cnf(c_0_389,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_390,negated_conjecture,
    ( esk6_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_278,c_0_387]),c_0_282])).

cnf(c_0_391,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | ~ r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_388])).

cnf(c_0_392,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk8_0,esk9_0))
    | esk5_2(esk8_0,esk9_0) != k1_waybel_9(esk8_0,esk9_0)
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ l1_pre_topc(esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_389,c_0_390]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_22])]),c_0_28]),c_0_29])).

cnf(c_0_393,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0)
    | r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_391,c_0_188])).

cnf(c_0_394,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk8_0,esk9_0))
    | esk5_2(esk8_0,esk9_0) != k1_waybel_9(esk8_0,esk9_0)
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_392,c_0_32]),c_0_17])])).

cnf(c_0_395,negated_conjecture,
    ( esk5_2(esk8_0,esk9_0) = k1_waybel_9(esk8_0,esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_287,c_0_393]),c_0_292])).

cnf(c_0_396,negated_conjecture,
    ( r2_hidden(X1,k10_yellow_6(esk8_0,esk9_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_394,c_0_395])])).

cnf(c_0_397,negated_conjecture,
    ( r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_396,c_0_59]),c_0_55])])).

cnf(c_0_398,negated_conjecture,
    ( m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_397])])).

cnf(c_0_399,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_398]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_400,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_397])])).

cnf(c_0_401,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_399,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_400])).

cnf(c_0_402,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_401,c_0_59]),c_0_55])])).

cnf(c_0_403,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_398]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_404,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_402])).

cnf(c_0_405,negated_conjecture,
    ( ~ r2_waybel_9(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_397])])).

cnf(c_0_406,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_403,c_0_22]),c_0_23]),c_0_25])]),c_0_28]),c_0_400])).

cnf(c_0_407,negated_conjecture,
    ( m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_404]),c_0_22]),c_0_20])]),c_0_405])).

cnf(c_0_408,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_406,c_0_59]),c_0_55])])).

cnf(c_0_409,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_407])).

cnf(c_0_410,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_408,c_0_409])).

cnf(c_0_411,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_410])).

cnf(c_0_412,negated_conjecture,
    ( m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_411]),c_0_22]),c_0_20])]),c_0_405])).

cnf(c_0_413,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_412])).

cnf(c_0_414,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_413])])).

cnf(c_0_415,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_414])).

cnf(c_0_416,negated_conjecture,
    ( m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_415]),c_0_22]),c_0_20])]),c_0_405])).

cnf(c_0_417,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_414])).

cnf(c_0_418,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_416]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_419,negated_conjecture,
    ( r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_417]),c_0_22]),c_0_20])]),c_0_405])).

cnf(c_0_420,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_418,c_0_22]),c_0_23]),c_0_25]),c_0_419])]),c_0_28])).

cnf(c_0_421,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | ~ r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_414])).

cnf(c_0_422,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_420,c_0_59]),c_0_55])])).

cnf(c_0_423,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk8_0,X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ l1_waybel_0(X2,esk8_0)
    | ~ r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_416]),c_0_24]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_27]),c_0_17]),c_0_39]),c_0_15])])).

cnf(c_0_424,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))
    | m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_421,c_0_422])).

cnf(c_0_425,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)
    | ~ r3_waybel_9(esk8_0,esk9_0,X1)
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_423,c_0_22]),c_0_23]),c_0_25]),c_0_419])]),c_0_28])).

cnf(c_0_426,negated_conjecture,
    ( m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_424]),c_0_22]),c_0_20])]),c_0_405])).

cnf(c_0_427,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))
    | ~ v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_425,c_0_59]),c_0_55])])).

cnf(c_0_428,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_426])).

cnf(c_0_429,negated_conjecture,
    ( r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_427,c_0_428])])).

cnf(c_0_430,negated_conjecture,
    ( r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_421,c_0_429])])).

cnf(c_0_431,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_430]),c_0_22]),c_0_20])]),c_0_405]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:44:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.66/0.84  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.66/0.84  # and selection function SelectNewComplexAHP.
% 0.66/0.84  #
% 0.66/0.84  # Preprocessing time       : 0.030 s
% 0.66/0.84  # Presaturation interreduction done
% 0.66/0.84  
% 0.66/0.84  # Proof found!
% 0.66/0.84  # SZS status Theorem
% 0.66/0.84  # SZS output start CNFRefutation
% 0.66/0.84  fof(t39_waybel_9, conjecture, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>(![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X2),X1,X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v11_waybel_0(X2,X1)=>(r2_waybel_9(X1,X2)&r2_hidden(k1_waybel_9(X1,X2),k10_yellow_6(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_waybel_9)).
% 0.66/0.84  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.66/0.84  fof(dt_l1_waybel_9, axiom, ![X1]:(l1_waybel_9(X1)=>(l1_pre_topc(X1)&l1_orders_2(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 0.66/0.84  fof(t30_waybel_9, axiom, ![X1]:(((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&v1_compts_1(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&r3_waybel_9(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_waybel_9)).
% 0.66/0.84  fof(t36_waybel_9, axiom, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(((![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X4),X1,X1))&v11_waybel_0(X3,X1))&r3_waybel_9(X1,X3,X2))=>X2=k1_waybel_9(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_waybel_9)).
% 0.66/0.84  fof(l51_waybel_9, axiom, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((((X3=X4&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X5),X1,X1)))&v11_waybel_0(X2,X1))&r3_waybel_9(X1,X2,X3))=>r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_waybel_9)).
% 0.66/0.84  fof(t31_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k2_yellow_0(X1,X3)&r2_yellow_0(X1,X3))=>(r1_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X3,X4)=>r1_orders_2(X1,X4,X2)))))&((r1_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X3,X4)=>r1_orders_2(X1,X4,X2))))=>(X2=k2_yellow_0(X1,X3)&r2_yellow_0(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_yellow_0)).
% 0.66/0.84  fof(t33_waybel_9, axiom, ![X1]:(((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&v1_compts_1(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r3_waybel_9(X1,X2,X3)&r3_waybel_9(X1,X2,X4))=>X3=X4)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)=>r2_hidden(X3,k10_yellow_6(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_waybel_9)).
% 0.66/0.84  fof(d4_waybel_9, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_waybel_0(X2,X1)=>(r2_waybel_9(X1,X2)<=>r2_yellow_0(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_waybel_9)).
% 0.66/0.84  fof(l52_waybel_9, axiom, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((X3=X4&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X5),X1,X1)))&r3_waybel_9(X1,X2,X3))=>![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)=>r1_orders_2(X1,X5,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l52_waybel_9)).
% 0.66/0.84  fof(c_0_10, negated_conjecture, ~(![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>(![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X2),X1,X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>(v11_waybel_0(X2,X1)=>(r2_waybel_9(X1,X2)&r2_hidden(k1_waybel_9(X1,X2),k10_yellow_6(X1,X2)))))))), inference(assume_negation,[status(cth)],[t39_waybel_9])).
% 0.66/0.84  fof(c_0_11, plain, ![X6]:(~l1_orders_2(X6)|(~v1_lattice3(X6)|~v2_struct_0(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.66/0.84  fof(c_0_12, negated_conjecture, ![X40]:(((((((((v2_pre_topc(esk8_0)&v8_pre_topc(esk8_0))&v3_orders_2(esk8_0))&v4_orders_2(esk8_0))&v5_orders_2(esk8_0))&v1_lattice3(esk8_0))&v2_lattice3(esk8_0))&v1_compts_1(esk8_0))&l1_waybel_9(esk8_0))&((~m1_subset_1(X40,u1_struct_0(esk8_0))|v5_pre_topc(k4_waybel_1(esk8_0,X40),esk8_0,esk8_0))&((((~v2_struct_0(esk9_0)&v4_orders_2(esk9_0))&v7_waybel_0(esk9_0))&l1_waybel_0(esk9_0,esk8_0))&(v11_waybel_0(esk9_0,esk8_0)&(~r2_waybel_9(esk8_0,esk9_0)|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).
% 0.66/0.84  fof(c_0_13, plain, ![X15]:((l1_pre_topc(X15)|~l1_waybel_9(X15))&(l1_orders_2(X15)|~l1_waybel_9(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).
% 0.66/0.84  cnf(c_0_14, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.66/0.84  cnf(c_0_15, negated_conjecture, (v1_lattice3(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.66/0.84  cnf(c_0_16, plain, (l1_orders_2(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.66/0.84  cnf(c_0_17, negated_conjecture, (l1_waybel_9(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.66/0.84  fof(c_0_18, plain, ![X27, X28]:((m1_subset_1(esk4_2(X27,X28),u1_struct_0(X27))|(v2_struct_0(X28)|~v4_orders_2(X28)|~v7_waybel_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~v8_pre_topc(X27)|~v1_compts_1(X27)|~l1_pre_topc(X27)))&(r3_waybel_9(X27,X28,esk4_2(X27,X28))|(v2_struct_0(X28)|~v4_orders_2(X28)|~v7_waybel_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~v8_pre_topc(X27)|~v1_compts_1(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_waybel_9])])])])])])).
% 0.66/0.84  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk8_0)|~l1_orders_2(esk8_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.66/0.84  cnf(c_0_20, negated_conjecture, (l1_orders_2(esk8_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.66/0.84  cnf(c_0_21, plain, (m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.66/0.84  cnf(c_0_22, negated_conjecture, (l1_waybel_0(esk9_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.66/0.84  cnf(c_0_23, negated_conjecture, (v7_waybel_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.66/0.84  cnf(c_0_24, negated_conjecture, (v1_compts_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.66/0.84  cnf(c_0_25, negated_conjecture, (v4_orders_2(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.66/0.84  cnf(c_0_26, negated_conjecture, (v8_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.66/0.84  cnf(c_0_27, negated_conjecture, (v2_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.66/0.84  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.66/0.84  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20])])).
% 0.66/0.84  fof(c_0_30, plain, ![X35, X36, X37]:((m1_subset_1(esk7_3(X35,X36,X37),u1_struct_0(X35))|~v11_waybel_0(X37,X35)|~r3_waybel_9(X35,X37,X36)|X36=k1_waybel_9(X35,X37)|(v2_struct_0(X37)|~v4_orders_2(X37)|~v7_waybel_0(X37)|~l1_waybel_0(X37,X35))|~m1_subset_1(X36,u1_struct_0(X35))|(~v2_pre_topc(X35)|~v8_pre_topc(X35)|~v3_orders_2(X35)|~v4_orders_2(X35)|~v5_orders_2(X35)|~v1_lattice3(X35)|~v2_lattice3(X35)|~v1_compts_1(X35)|~l1_waybel_9(X35)))&(~v5_pre_topc(k4_waybel_1(X35,esk7_3(X35,X36,X37)),X35,X35)|~v11_waybel_0(X37,X35)|~r3_waybel_9(X35,X37,X36)|X36=k1_waybel_9(X35,X37)|(v2_struct_0(X37)|~v4_orders_2(X37)|~v7_waybel_0(X37)|~l1_waybel_0(X37,X35))|~m1_subset_1(X36,u1_struct_0(X35))|(~v2_pre_topc(X35)|~v8_pre_topc(X35)|~v3_orders_2(X35)|~v4_orders_2(X35)|~v5_orders_2(X35)|~v1_lattice3(X35)|~v2_lattice3(X35)|~v1_compts_1(X35)|~l1_waybel_9(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_waybel_9])])])])])])).
% 0.66/0.84  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~l1_pre_topc(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27])]), c_0_28]), c_0_29])).
% 0.66/0.84  cnf(c_0_32, plain, (l1_pre_topc(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.66/0.84  cnf(c_0_33, plain, (r3_waybel_9(X1,X2,esk4_2(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.66/0.84  cnf(c_0_34, plain, (m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))|X2=k1_waybel_9(X1,X3)|v2_struct_0(X3)|~v11_waybel_0(X3,X1)|~r3_waybel_9(X1,X3,X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.66/0.84  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk4_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_17])])).
% 0.66/0.84  cnf(c_0_36, negated_conjecture, (v2_lattice3(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.66/0.84  cnf(c_0_37, negated_conjecture, (v4_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.66/0.84  cnf(c_0_38, negated_conjecture, (v3_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.66/0.84  cnf(c_0_39, negated_conjecture, (v5_orders_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.66/0.84  cnf(c_0_40, negated_conjecture, (r3_waybel_9(esk8_0,esk9_0,esk4_2(esk8_0,esk9_0))|~l1_pre_topc(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27])]), c_0_28]), c_0_29])).
% 0.66/0.84  cnf(c_0_41, plain, (X2=k1_waybel_9(X1,X3)|v2_struct_0(X3)|~v5_pre_topc(k4_waybel_1(X1,esk7_3(X1,X2,X3)),X1,X1)|~v11_waybel_0(X3,X1)|~r3_waybel_9(X1,X3,X2)|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.66/0.84  cnf(c_0_42, negated_conjecture, (esk4_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,X1)|m1_subset_1(esk7_3(esk8_0,esk4_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))|~v11_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_43, negated_conjecture, (v11_waybel_0(esk9_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.66/0.84  cnf(c_0_44, negated_conjecture, (r3_waybel_9(esk8_0,esk9_0,esk4_2(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_32]), c_0_17])])).
% 0.66/0.84  cnf(c_0_45, negated_conjecture, (esk4_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))|~v11_waybel_0(X1,esk8_0)|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk4_2(esk8_0,esk9_0),X1)),esk8_0,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_35]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  fof(c_0_46, plain, ![X16, X17, X18, X19]:((m1_subset_1(esk2_4(X16,X17,X18,X19),u1_struct_0(X16))|X18!=X19|~v11_waybel_0(X17,X16)|~r3_waybel_9(X16,X17,X18)|r1_lattice3(X16,k2_relset_1(u1_struct_0(X17),u1_struct_0(X16),u1_waybel_0(X16,X17)),X19)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|(v2_struct_0(X17)|~v4_orders_2(X17)|~v7_waybel_0(X17)|~l1_waybel_0(X17,X16))|(~v2_pre_topc(X16)|~v8_pre_topc(X16)|~v3_orders_2(X16)|~v4_orders_2(X16)|~v5_orders_2(X16)|~v1_lattice3(X16)|~v2_lattice3(X16)|~v1_compts_1(X16)|~l1_waybel_9(X16)))&(~v5_pre_topc(k4_waybel_1(X16,esk2_4(X16,X17,X18,X19)),X16,X16)|X18!=X19|~v11_waybel_0(X17,X16)|~r3_waybel_9(X16,X17,X18)|r1_lattice3(X16,k2_relset_1(u1_struct_0(X17),u1_struct_0(X16),u1_waybel_0(X16,X17)),X19)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|(v2_struct_0(X17)|~v4_orders_2(X17)|~v7_waybel_0(X17)|~l1_waybel_0(X17,X16))|(~v2_pre_topc(X16)|~v8_pre_topc(X16)|~v3_orders_2(X16)|~v4_orders_2(X16)|~v5_orders_2(X16)|~v1_lattice3(X16)|~v2_lattice3(X16)|~v1_compts_1(X16)|~l1_waybel_9(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l51_waybel_9])])])])])])).
% 0.66/0.84  cnf(c_0_47, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,X1),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.66/0.84  cnf(c_0_48, negated_conjecture, (esk4_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk4_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_23]), c_0_25]), c_0_22])]), c_0_28])).
% 0.66/0.84  cnf(c_0_49, negated_conjecture, (esk4_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk4_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_43]), c_0_44]), c_0_23]), c_0_25]), c_0_22])]), c_0_28])).
% 0.66/0.84  fof(c_0_50, plain, ![X7, X8, X9, X10, X11]:(((r1_lattice3(X7,X9,X8)|(X8!=k2_yellow_0(X7,X9)|~r2_yellow_0(X7,X9))|~m1_subset_1(X8,u1_struct_0(X7))|(~v5_orders_2(X7)|~l1_orders_2(X7)))&(~m1_subset_1(X10,u1_struct_0(X7))|(~r1_lattice3(X7,X9,X10)|r1_orders_2(X7,X10,X8))|(X8!=k2_yellow_0(X7,X9)|~r2_yellow_0(X7,X9))|~m1_subset_1(X8,u1_struct_0(X7))|(~v5_orders_2(X7)|~l1_orders_2(X7))))&(((X8=k2_yellow_0(X7,X11)|(m1_subset_1(esk1_3(X7,X8,X11),u1_struct_0(X7))|~r1_lattice3(X7,X11,X8))|~m1_subset_1(X8,u1_struct_0(X7))|(~v5_orders_2(X7)|~l1_orders_2(X7)))&(r2_yellow_0(X7,X11)|(m1_subset_1(esk1_3(X7,X8,X11),u1_struct_0(X7))|~r1_lattice3(X7,X11,X8))|~m1_subset_1(X8,u1_struct_0(X7))|(~v5_orders_2(X7)|~l1_orders_2(X7))))&(((X8=k2_yellow_0(X7,X11)|(r1_lattice3(X7,X11,esk1_3(X7,X8,X11))|~r1_lattice3(X7,X11,X8))|~m1_subset_1(X8,u1_struct_0(X7))|(~v5_orders_2(X7)|~l1_orders_2(X7)))&(r2_yellow_0(X7,X11)|(r1_lattice3(X7,X11,esk1_3(X7,X8,X11))|~r1_lattice3(X7,X11,X8))|~m1_subset_1(X8,u1_struct_0(X7))|(~v5_orders_2(X7)|~l1_orders_2(X7))))&((X8=k2_yellow_0(X7,X11)|(~r1_orders_2(X7,esk1_3(X7,X8,X11),X8)|~r1_lattice3(X7,X11,X8))|~m1_subset_1(X8,u1_struct_0(X7))|(~v5_orders_2(X7)|~l1_orders_2(X7)))&(r2_yellow_0(X7,X11)|(~r1_orders_2(X7,esk1_3(X7,X8,X11),X8)|~r1_lattice3(X7,X11,X8))|~m1_subset_1(X8,u1_struct_0(X7))|(~v5_orders_2(X7)|~l1_orders_2(X7))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_yellow_0])])])])])])).
% 0.66/0.84  cnf(c_0_51, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X1))|r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)|v2_struct_0(X2)|X3!=X4|~v11_waybel_0(X2,X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.66/0.84  cnf(c_0_52, negated_conjecture, (esk4_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.66/0.84  cnf(c_0_53, plain, (r2_yellow_0(X1,X2)|m1_subset_1(esk1_3(X1,X3,X2),u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.66/0.84  cnf(c_0_54, plain, (r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)|m1_subset_1(esk2_4(X1,X2,X3,X3),u1_struct_0(X1))|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~v11_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X2)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)), inference(er,[status(thm)],[c_0_51])).
% 0.66/0.84  cnf(c_0_55, negated_conjecture, (m1_subset_1(k1_waybel_9(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(rw,[status(thm)],[c_0_35, c_0_52])).
% 0.66/0.84  fof(c_0_56, plain, ![X30, X31, X34]:((m1_subset_1(esk5_2(X30,X31),u1_struct_0(X30))|(~m1_subset_1(X34,u1_struct_0(X30))|(~r3_waybel_9(X30,X31,X34)|r2_hidden(X34,k10_yellow_6(X30,X31))))|(v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~l1_waybel_0(X31,X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~v8_pre_topc(X30)|~v1_compts_1(X30)|~l1_pre_topc(X30)))&((m1_subset_1(esk6_2(X30,X31),u1_struct_0(X30))|(~m1_subset_1(X34,u1_struct_0(X30))|(~r3_waybel_9(X30,X31,X34)|r2_hidden(X34,k10_yellow_6(X30,X31))))|(v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~l1_waybel_0(X31,X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~v8_pre_topc(X30)|~v1_compts_1(X30)|~l1_pre_topc(X30)))&(((r3_waybel_9(X30,X31,esk5_2(X30,X31))|(~m1_subset_1(X34,u1_struct_0(X30))|(~r3_waybel_9(X30,X31,X34)|r2_hidden(X34,k10_yellow_6(X30,X31))))|(v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~l1_waybel_0(X31,X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~v8_pre_topc(X30)|~v1_compts_1(X30)|~l1_pre_topc(X30)))&(r3_waybel_9(X30,X31,esk6_2(X30,X31))|(~m1_subset_1(X34,u1_struct_0(X30))|(~r3_waybel_9(X30,X31,X34)|r2_hidden(X34,k10_yellow_6(X30,X31))))|(v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~l1_waybel_0(X31,X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~v8_pre_topc(X30)|~v1_compts_1(X30)|~l1_pre_topc(X30))))&(esk5_2(X30,X31)!=esk6_2(X30,X31)|(~m1_subset_1(X34,u1_struct_0(X30))|(~r3_waybel_9(X30,X31,X34)|r2_hidden(X34,k10_yellow_6(X30,X31))))|(v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~l1_waybel_0(X31,X30))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~v8_pre_topc(X30)|~v1_compts_1(X30)|~l1_pre_topc(X30)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t33_waybel_9])])])])])])).
% 0.66/0.84  cnf(c_0_57, negated_conjecture, (r2_yellow_0(esk8_0,X1)|m1_subset_1(esk1_3(esk8_0,esk4_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))|~r1_lattice3(esk8_0,X1,esk4_2(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_35]), c_0_39]), c_0_20])])).
% 0.66/0.84  cnf(c_0_58, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X1)),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0))|~v11_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_59, negated_conjecture, (r3_waybel_9(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0))), inference(rw,[status(thm)],[c_0_44, c_0_52])).
% 0.66/0.84  cnf(c_0_60, plain, (m1_subset_1(esk6_2(X1,X2),u1_struct_0(X1))|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.66/0.84  cnf(c_0_61, plain, (r2_yellow_0(X1,X2)|r1_lattice3(X1,X2,esk1_3(X1,X3,X2))|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.66/0.84  fof(c_0_62, plain, ![X13, X14]:((~r2_waybel_9(X13,X14)|r2_yellow_0(X13,k2_relset_1(u1_struct_0(X14),u1_struct_0(X13),u1_waybel_0(X13,X14)))|~l1_waybel_0(X14,X13)|~l1_orders_2(X13))&(~r2_yellow_0(X13,k2_relset_1(u1_struct_0(X14),u1_struct_0(X13),u1_waybel_0(X13,X14)))|r2_waybel_9(X13,X14)|~l1_waybel_0(X14,X13)|~l1_orders_2(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_waybel_9])])])])).
% 0.66/0.84  cnf(c_0_63, negated_conjecture, (r2_yellow_0(esk8_0,X1)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))|~r1_lattice3(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_52]), c_0_52])).
% 0.66/0.84  cnf(c_0_64, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_43]), c_0_59]), c_0_23]), c_0_25]), c_0_22])]), c_0_28])).
% 0.66/0.84  cnf(c_0_65, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))|m1_subset_1(esk6_2(esk8_0,X1),u1_struct_0(esk8_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_pre_topc(esk8_0)|~l1_waybel_0(X1,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_35]), c_0_24]), c_0_26]), c_0_27])]), c_0_29])).
% 0.66/0.84  cnf(c_0_66, negated_conjecture, (r1_lattice3(esk8_0,X1,esk1_3(esk8_0,esk4_2(esk8_0,esk9_0),X1))|r2_yellow_0(esk8_0,X1)|~r1_lattice3(esk8_0,X1,esk4_2(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_35]), c_0_39]), c_0_20])])).
% 0.66/0.84  cnf(c_0_67, plain, (r2_waybel_9(X1,X2)|~r2_yellow_0(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))|~l1_waybel_0(X2,X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.66/0.84  cnf(c_0_68, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.66/0.84  cnf(c_0_69, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))|m1_subset_1(esk6_2(esk8_0,X1),u1_struct_0(esk8_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_32]), c_0_17])])).
% 0.66/0.84  cnf(c_0_70, negated_conjecture, (r1_lattice3(esk8_0,X1,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),X1))|r2_yellow_0(esk8_0,X1)|~r1_lattice3(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_52]), c_0_52])).
% 0.66/0.84  cnf(c_0_71, plain, (m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.66/0.84  fof(c_0_72, plain, ![X21, X22, X23, X24, X26]:((m1_subset_1(esk3_4(X21,X22,X23,X24),u1_struct_0(X21))|X23!=X24|~r3_waybel_9(X21,X22,X23)|(~m1_subset_1(X26,u1_struct_0(X21))|(~r1_lattice3(X21,k2_relset_1(u1_struct_0(X22),u1_struct_0(X21),u1_waybel_0(X21,X22)),X26)|r1_orders_2(X21,X26,X24)))|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~l1_waybel_0(X22,X21))|(~v2_pre_topc(X21)|~v8_pre_topc(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~v1_lattice3(X21)|~v2_lattice3(X21)|~v1_compts_1(X21)|~l1_waybel_9(X21)))&(~v5_pre_topc(k4_waybel_1(X21,esk3_4(X21,X22,X23,X24)),X21,X21)|X23!=X24|~r3_waybel_9(X21,X22,X23)|(~m1_subset_1(X26,u1_struct_0(X21))|(~r1_lattice3(X21,k2_relset_1(u1_struct_0(X22),u1_struct_0(X21),u1_waybel_0(X21,X22)),X26)|r1_orders_2(X21,X26,X24)))|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~l1_waybel_0(X22,X21))|(~v2_pre_topc(X21)|~v8_pre_topc(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~v1_lattice3(X21)|~v2_lattice3(X21)|~v1_compts_1(X21)|~l1_waybel_9(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l52_waybel_9])])])])])])).
% 0.66/0.84  cnf(c_0_73, negated_conjecture, (~r2_waybel_9(esk8_0,esk9_0)|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.66/0.84  cnf(c_0_74, negated_conjecture, (r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_75, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_22]), c_0_44]), c_0_23]), c_0_25])]), c_0_28])).
% 0.66/0.84  cnf(c_0_76, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_70, c_0_64])).
% 0.66/0.84  cnf(c_0_77, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))|m1_subset_1(esk5_2(esk8_0,X1),u1_struct_0(esk8_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_pre_topc(esk8_0)|~l1_waybel_0(X1,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_35]), c_0_24]), c_0_26]), c_0_27])]), c_0_29])).
% 0.66/0.84  cnf(c_0_78, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X1))|r1_orders_2(X1,X5,X4)|v2_struct_0(X2)|X3!=X4|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X5,u1_struct_0(X1))|~r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.66/0.84  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.66/0.84  cnf(c_0_80, negated_conjecture, (r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(rw,[status(thm)],[c_0_75, c_0_52])).
% 0.66/0.84  cnf(c_0_81, negated_conjecture, (r2_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_76]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_82, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))|m1_subset_1(esk5_2(esk8_0,X1),u1_struct_0(esk8_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk4_2(esk8_0,esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_32]), c_0_17])])).
% 0.66/0.84  cnf(c_0_83, plain, (r2_yellow_0(X1,X2)|~r1_orders_2(X1,esk1_3(X1,X3,X2),X3)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.66/0.84  cnf(c_0_84, plain, (r1_orders_2(X1,X2,X3)|m1_subset_1(esk3_4(X1,X4,X3,X3),u1_struct_0(X1))|v2_struct_0(X4)|~r3_waybel_9(X1,X4,X3)|~v7_waybel_0(X4)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X4)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X4,X1)|~r1_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)), inference(er,[status(thm)],[c_0_78])).
% 0.66/0.84  cnf(c_0_85, negated_conjecture, (m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.66/0.84  cnf(c_0_86, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_81])).
% 0.66/0.84  cnf(c_0_87, negated_conjecture, (r2_hidden(esk4_2(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_22]), c_0_44]), c_0_23]), c_0_25])]), c_0_28])).
% 0.66/0.84  cnf(c_0_88, negated_conjecture, (r2_yellow_0(esk8_0,X1)|~r1_orders_2(esk8_0,esk1_3(esk8_0,esk4_2(esk8_0,esk9_0),X1),esk4_2(esk8_0,esk9_0))|~r1_lattice3(esk8_0,X1,esk4_2(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_35]), c_0_39]), c_0_20])])).
% 0.66/0.84  cnf(c_0_89, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_90, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_86, c_0_80])).
% 0.66/0.84  cnf(c_0_91, negated_conjecture, (r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(rw,[status(thm)],[c_0_87, c_0_52])).
% 0.66/0.84  cnf(c_0_92, negated_conjecture, (r2_yellow_0(esk8_0,X1)|~r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),X1),k1_waybel_9(esk8_0,esk9_0))|~r1_lattice3(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_52]), c_0_52]), c_0_52])).
% 0.66/0.84  cnf(c_0_93, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_90])).
% 0.66/0.84  cnf(c_0_94, negated_conjecture, (m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_79, c_0_91])).
% 0.66/0.84  cnf(c_0_95, plain, (r1_orders_2(X1,X5,X4)|v2_struct_0(X2)|~v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X2,X3,X4)),X1,X1)|X3!=X4|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X5,u1_struct_0(X1))|~r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.66/0.84  cnf(c_0_96, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_92, c_0_64])).
% 0.66/0.84  cnf(c_0_97, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_98, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_94]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_99, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_86, c_0_91])).
% 0.66/0.84  cnf(c_0_100, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X4)|~r3_waybel_9(X1,X4,X3)|~v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X4,X3,X3)),X1,X1)|~v7_waybel_0(X4)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X4)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X4,X1)|~r1_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)), inference(er,[status(thm)],[c_0_95])).
% 0.66/0.84  cnf(c_0_101, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.66/0.84  cnf(c_0_102, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_99])).
% 0.66/0.84  cnf(c_0_103, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_85]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_104, negated_conjecture, (r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_101]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_105, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_106, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_90])).
% 0.66/0.84  cnf(c_0_107, negated_conjecture, (m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_104]), c_0_80])).
% 0.66/0.84  cnf(c_0_108, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_96, c_0_105])).
% 0.66/0.84  cnf(c_0_109, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_110, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_107])).
% 0.66/0.84  cnf(c_0_111, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_94]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_112, negated_conjecture, (r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_108]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_113, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 0.66/0.84  cnf(c_0_114, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_99])).
% 0.66/0.84  cnf(c_0_115, negated_conjecture, (m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_112]), c_0_91])).
% 0.66/0.84  cnf(c_0_116, plain, (r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)|v2_struct_0(X2)|~v5_pre_topc(k4_waybel_1(X1,esk2_4(X1,X2,X3,X4)),X1,X1)|X3!=X4|~v11_waybel_0(X2,X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.66/0.84  cnf(c_0_117, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_96, c_0_113])).
% 0.66/0.84  cnf(c_0_118, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_119, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_115])).
% 0.66/0.84  cnf(c_0_120, plain, (r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~v11_waybel_0(X2,X1)|~v5_pre_topc(k4_waybel_1(X1,esk2_4(X1,X2,X3,X3)),X1,X1)|~v7_waybel_0(X2)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X2)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)), inference(er,[status(thm)],[c_0_116])).
% 0.66/0.84  cnf(c_0_121, negated_conjecture, (r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_117]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_122, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 0.66/0.84  cnf(c_0_123, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X1),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X1)),k1_waybel_9(esk8_0,esk9_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0))|~v11_waybel_0(X1,esk8_0)|~v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_55]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_124, negated_conjecture, (m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_121]), c_0_80])).
% 0.66/0.84  cnf(c_0_125, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_96, c_0_122])).
% 0.66/0.84  cnf(c_0_126, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_43]), c_0_59]), c_0_23]), c_0_25]), c_0_22])]), c_0_28])).
% 0.66/0.84  cnf(c_0_127, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_124])).
% 0.66/0.84  cnf(c_0_128, negated_conjecture, (r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_125]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_129, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 0.66/0.84  cnf(c_0_130, negated_conjecture, (m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_128]), c_0_91])).
% 0.66/0.84  cnf(c_0_131, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_63, c_0_129])).
% 0.66/0.84  cnf(c_0_132, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_130])).
% 0.66/0.84  cnf(c_0_133, negated_conjecture, (r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_131]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_134, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_70, c_0_129])).
% 0.66/0.84  cnf(c_0_135, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_126, c_0_132])).
% 0.66/0.84  cnf(c_0_136, negated_conjecture, (m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_133]), c_0_80])).
% 0.66/0.84  cnf(c_0_137, negated_conjecture, (r2_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_134]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_138, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_63, c_0_135])).
% 0.66/0.84  cnf(c_0_139, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_136]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_140, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_137]), c_0_80])).
% 0.66/0.84  cnf(c_0_141, negated_conjecture, (r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_138]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_142, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_70, c_0_135])).
% 0.66/0.84  cnf(c_0_143, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_140])).
% 0.66/0.84  cnf(c_0_144, negated_conjecture, (m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_141]), c_0_91])).
% 0.66/0.84  cnf(c_0_145, negated_conjecture, (r2_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_142]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_146, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_92, c_0_129])).
% 0.66/0.84  cnf(c_0_147, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_148, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_144]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_149, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_145]), c_0_91])).
% 0.66/0.84  cnf(c_0_150, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_146, c_0_147])).
% 0.66/0.84  cnf(c_0_151, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_149])).
% 0.66/0.84  cnf(c_0_152, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_136]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_153, negated_conjecture, (r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_150]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_154, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_92, c_0_135])).
% 0.66/0.84  cnf(c_0_155, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_156, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_140])).
% 0.66/0.84  cnf(c_0_157, negated_conjecture, (m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_153]), c_0_80])).
% 0.66/0.84  cnf(c_0_158, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_154, c_0_155])).
% 0.66/0.84  cnf(c_0_159, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_160, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_157])).
% 0.66/0.84  cnf(c_0_161, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_144]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_162, negated_conjecture, (r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_158]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_163, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_159, c_0_160])).
% 0.66/0.84  cnf(c_0_164, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_149])).
% 0.66/0.84  cnf(c_0_165, negated_conjecture, (m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_162]), c_0_91])).
% 0.66/0.84  cnf(c_0_166, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_146, c_0_163])).
% 0.66/0.84  cnf(c_0_167, plain, (r3_waybel_9(X1,X2,esk6_2(X1,X2))|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.66/0.84  cnf(c_0_168, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_169, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_165])).
% 0.66/0.84  cnf(c_0_170, negated_conjecture, (r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_166]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_171, negated_conjecture, (r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))|r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,X1))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_pre_topc(esk8_0)|~l1_waybel_0(X1,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167, c_0_55]), c_0_24]), c_0_26]), c_0_27])]), c_0_29])).
% 0.66/0.84  cnf(c_0_172, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_168, c_0_169])).
% 0.66/0.84  cnf(c_0_173, negated_conjecture, (m1_subset_1(esk6_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_170]), c_0_80])).
% 0.66/0.84  cnf(c_0_174, negated_conjecture, (r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))|r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,X1))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_32]), c_0_17])])).
% 0.66/0.84  cnf(c_0_175, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_154, c_0_172])).
% 0.66/0.84  cnf(c_0_176, plain, (r3_waybel_9(X1,X2,esk5_2(X1,X2))|r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.66/0.84  cnf(c_0_177, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,X1)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,esk9_0))|~v11_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_173]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_178, negated_conjecture, (r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))|r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_22]), c_0_59]), c_0_23]), c_0_25])]), c_0_28])).
% 0.66/0.84  cnf(c_0_179, negated_conjecture, (r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_175]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_180, negated_conjecture, (r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))|r3_waybel_9(esk8_0,X1,esk5_2(esk8_0,X1))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_pre_topc(esk8_0)|~l1_waybel_0(X1,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176, c_0_55]), c_0_24]), c_0_26]), c_0_27])]), c_0_29])).
% 0.66/0.84  cnf(c_0_181, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177, c_0_43]), c_0_23]), c_0_25]), c_0_22])]), c_0_28])).
% 0.66/0.84  cnf(c_0_182, negated_conjecture, (r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_79, c_0_178])).
% 0.66/0.84  cnf(c_0_183, negated_conjecture, (m1_subset_1(esk5_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_179]), c_0_91])).
% 0.66/0.84  cnf(c_0_184, negated_conjecture, (r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,X1))|r3_waybel_9(esk8_0,X1,esk5_2(esk8_0,X1))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,k1_waybel_9(esk8_0,esk9_0))|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180, c_0_32]), c_0_17])])).
% 0.66/0.84  cnf(c_0_185, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_181, c_0_182])).
% 0.66/0.84  cnf(c_0_186, negated_conjecture, (r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_86, c_0_178])).
% 0.66/0.84  cnf(c_0_187, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,X1)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),X1),u1_struct_0(esk8_0))|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk5_2(esk8_0,esk9_0))|~v11_waybel_0(X1,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_183]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_188, negated_conjecture, (r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))|r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184, c_0_22]), c_0_59]), c_0_23]), c_0_25])]), c_0_28])).
% 0.66/0.84  cnf(c_0_189, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_185]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_190, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_181, c_0_186])).
% 0.66/0.84  cnf(c_0_191, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187, c_0_43]), c_0_23]), c_0_25]), c_0_22])]), c_0_28])).
% 0.66/0.84  cnf(c_0_192, negated_conjecture, (r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_79, c_0_188])).
% 0.66/0.84  cnf(c_0_193, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_190])).
% 0.66/0.84  cnf(c_0_194, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_191, c_0_192])).
% 0.66/0.84  cnf(c_0_195, negated_conjecture, (r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_86, c_0_188])).
% 0.66/0.84  cnf(c_0_196, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_197, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_194]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_198, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_191, c_0_195])).
% 0.66/0.84  cnf(c_0_199, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_96, c_0_196])).
% 0.66/0.84  cnf(c_0_200, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_198])).
% 0.66/0.84  cnf(c_0_201, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_199]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_202, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_200, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_203, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_185]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_204, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_201])).
% 0.66/0.84  cnf(c_0_205, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_96, c_0_202])).
% 0.66/0.84  cnf(c_0_206, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_190])).
% 0.66/0.84  cnf(c_0_207, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_204, c_0_178]), c_0_181])).
% 0.66/0.84  cnf(c_0_208, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_205]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_209, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_206, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_210, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_207])).
% 0.66/0.84  cnf(c_0_211, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_194]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_212, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_208])).
% 0.66/0.84  cnf(c_0_213, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_209, c_0_210])).
% 0.66/0.84  cnf(c_0_214, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_211, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_198])).
% 0.66/0.84  cnf(c_0_215, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_212, c_0_188]), c_0_191])).
% 0.66/0.84  cnf(c_0_216, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_96, c_0_213])).
% 0.66/0.84  cnf(c_0_217, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_214, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_218, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_215])).
% 0.66/0.84  cnf(c_0_219, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_216]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_220, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_217, c_0_218])).
% 0.66/0.84  cnf(c_0_221, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_219])).
% 0.66/0.84  cnf(c_0_222, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_96, c_0_220])).
% 0.66/0.84  cnf(c_0_223, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_221, c_0_178]), c_0_181])).
% 0.66/0.84  cnf(c_0_224, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_222]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_225, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_223])).
% 0.66/0.84  cnf(c_0_226, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_224])).
% 0.66/0.84  cnf(c_0_227, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_126, c_0_225])).
% 0.66/0.84  cnf(c_0_228, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_226, c_0_188]), c_0_191])).
% 0.66/0.84  cnf(c_0_229, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_63, c_0_227])).
% 0.66/0.84  cnf(c_0_230, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_228])).
% 0.66/0.84  cnf(c_0_231, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_229]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_232, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_70, c_0_227])).
% 0.66/0.84  cnf(c_0_233, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_126, c_0_230])).
% 0.66/0.84  cnf(c_0_234, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_231])).
% 0.66/0.84  cnf(c_0_235, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_232]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_236, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_63, c_0_233])).
% 0.66/0.84  cnf(c_0_237, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_234, c_0_178]), c_0_181])).
% 0.66/0.84  cnf(c_0_238, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_235])).
% 0.66/0.84  cnf(c_0_239, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_236]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_240, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_70, c_0_233])).
% 0.66/0.84  cnf(c_0_241, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_237]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_242, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_238, c_0_178]), c_0_181])).
% 0.66/0.84  cnf(c_0_243, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_239])).
% 0.66/0.84  cnf(c_0_244, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_240]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_245, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_241, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_242])).
% 0.66/0.84  cnf(c_0_246, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_188]), c_0_191])).
% 0.66/0.84  cnf(c_0_247, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_244])).
% 0.66/0.84  cnf(c_0_248, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_92, c_0_227])).
% 0.66/0.84  cnf(c_0_249, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_245, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_250, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_246]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_251, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_247, c_0_188]), c_0_191])).
% 0.66/0.84  cnf(c_0_252, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_248, c_0_249])).
% 0.66/0.84  cnf(c_0_253, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_250, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_251])).
% 0.66/0.84  cnf(c_0_254, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_252]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_255, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_92, c_0_233])).
% 0.66/0.84  cnf(c_0_256, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_253, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_257, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_237]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_258, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_254])).
% 0.66/0.84  cnf(c_0_259, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_255, c_0_256])).
% 0.66/0.84  cnf(c_0_260, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_257, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_242])).
% 0.66/0.84  cnf(c_0_261, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_258, c_0_178]), c_0_181])).
% 0.66/0.84  cnf(c_0_262, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_259]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_263, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_260, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_264, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_261])).
% 0.66/0.84  cnf(c_0_265, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_246]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_266, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_262])).
% 0.66/0.84  cnf(c_0_267, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_263, c_0_264])).
% 0.66/0.84  cnf(c_0_268, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_265, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_251])).
% 0.66/0.84  cnf(c_0_269, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_266, c_0_188]), c_0_191])).
% 0.66/0.84  cnf(c_0_270, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_248, c_0_267])).
% 0.66/0.84  cnf(c_0_271, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_268, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_272, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_269])).
% 0.66/0.84  cnf(c_0_273, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_270]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_274, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_271, c_0_272])).
% 0.66/0.84  cnf(c_0_275, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk6_2(esk8_0,esk9_0))|~v11_waybel_0(X1,esk8_0)|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),X1)),esk8_0,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_173]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_276, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_273])).
% 0.66/0.84  cnf(c_0_277, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_255, c_0_274])).
% 0.66/0.84  cnf(c_0_278, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|~r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_275, c_0_43]), c_0_23]), c_0_25]), c_0_22])]), c_0_28])).
% 0.66/0.84  cnf(c_0_279, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_276, c_0_178]), c_0_181])).
% 0.66/0.84  cnf(c_0_280, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_277]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_281, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_278, c_0_182])).
% 0.66/0.84  cnf(c_0_282, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_47, c_0_279])).
% 0.66/0.84  cnf(c_0_283, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,X1)|v2_struct_0(X1)|~r3_waybel_9(esk8_0,X1,esk5_2(esk8_0,esk9_0))|~v11_waybel_0(X1,esk8_0)|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),X1)),esk8_0,esk8_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_183]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_284, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_280])).
% 0.66/0.84  cnf(c_0_285, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_281, c_0_282])).
% 0.66/0.84  cnf(c_0_286, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk6_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_278, c_0_186])).
% 0.66/0.84  cnf(c_0_287, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|~r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_283, c_0_43]), c_0_23]), c_0_25]), c_0_22])]), c_0_28])).
% 0.66/0.84  cnf(c_0_288, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_284, c_0_188]), c_0_191])).
% 0.66/0.84  cnf(c_0_289, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_285]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_290, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_286, c_0_282])).
% 0.66/0.84  cnf(c_0_291, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_287, c_0_192])).
% 0.66/0.84  cnf(c_0_292, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_47, c_0_288])).
% 0.66/0.84  cnf(c_0_293, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_289, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_290])).
% 0.66/0.84  cnf(c_0_294, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_291, c_0_292])).
% 0.66/0.84  cnf(c_0_295, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk7_3(esk8_0,esk5_2(esk8_0,esk9_0),esk9_0)),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_287, c_0_195])).
% 0.66/0.84  cnf(c_0_296, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_293, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_297, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_294]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_298, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_295, c_0_292])).
% 0.66/0.84  cnf(c_0_299, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_96, c_0_296])).
% 0.66/0.84  cnf(c_0_300, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_297, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_298])).
% 0.66/0.84  cnf(c_0_301, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_299]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_302, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_300, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_303, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_301])).
% 0.66/0.84  cnf(c_0_304, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_96, c_0_302])).
% 0.66/0.84  cnf(c_0_305, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_285]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_306, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_303, c_0_178])).
% 0.66/0.84  cnf(c_0_307, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_304]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_308, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_305, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_290])).
% 0.66/0.84  cnf(c_0_309, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_278, c_0_306]), c_0_282])).
% 0.66/0.84  cnf(c_0_310, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_307])).
% 0.66/0.84  cnf(c_0_311, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_308, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_312, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_309])).
% 0.66/0.84  cnf(c_0_313, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_294]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_314, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_310, c_0_188])).
% 0.66/0.84  cnf(c_0_315, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_311, c_0_312])).
% 0.66/0.84  cnf(c_0_316, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_313, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_298])).
% 0.66/0.84  cnf(c_0_317, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_287, c_0_314]), c_0_292])).
% 0.66/0.84  cnf(c_0_318, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_96, c_0_315])).
% 0.66/0.84  cnf(c_0_319, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_316, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_320, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_317])).
% 0.66/0.84  cnf(c_0_321, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_318]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_322, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_319, c_0_320])).
% 0.66/0.84  cnf(c_0_323, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_321])).
% 0.66/0.84  cnf(c_0_324, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_96, c_0_322])).
% 0.66/0.84  cnf(c_0_325, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_323, c_0_178])).
% 0.66/0.84  cnf(c_0_326, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_324]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_327, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_278, c_0_325]), c_0_282])).
% 0.66/0.84  cnf(c_0_328, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_326])).
% 0.66/0.84  cnf(c_0_329, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_47, c_0_327])).
% 0.66/0.84  cnf(c_0_330, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_328, c_0_188])).
% 0.66/0.84  cnf(c_0_331, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_126, c_0_329])).
% 0.66/0.84  cnf(c_0_332, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_287, c_0_330]), c_0_292])).
% 0.66/0.84  cnf(c_0_333, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_63, c_0_331])).
% 0.66/0.84  cnf(c_0_334, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_47, c_0_332])).
% 0.66/0.84  cnf(c_0_335, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_333]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_336, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))), inference(spm,[status(thm)],[c_0_70, c_0_331])).
% 0.66/0.84  cnf(c_0_337, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_126, c_0_334])).
% 0.66/0.84  cnf(c_0_338, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_335])).
% 0.66/0.84  cnf(c_0_339, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_336]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_340, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_63, c_0_337])).
% 0.66/0.84  cnf(c_0_341, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_338, c_0_178])).
% 0.66/0.84  cnf(c_0_342, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_339])).
% 0.66/0.84  cnf(c_0_343, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_340]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_344, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))), inference(spm,[status(thm)],[c_0_70, c_0_337])).
% 0.66/0.84  cnf(c_0_345, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_278, c_0_341]), c_0_282])).
% 0.66/0.84  cnf(c_0_346, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_342, c_0_178])).
% 0.66/0.84  cnf(c_0_347, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_343])).
% 0.66/0.84  cnf(c_0_348, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_344]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_349, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_345]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_350, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_278, c_0_346]), c_0_282])).
% 0.66/0.84  cnf(c_0_351, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_347, c_0_188])).
% 0.66/0.84  cnf(c_0_352, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_348])).
% 0.66/0.84  cnf(c_0_353, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_349, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_350])).
% 0.66/0.84  cnf(c_0_354, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_287, c_0_351]), c_0_292])).
% 0.66/0.84  cnf(c_0_355, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(spm,[status(thm)],[c_0_352, c_0_188])).
% 0.66/0.84  cnf(c_0_356, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|~r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_92, c_0_331])).
% 0.66/0.84  cnf(c_0_357, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_353, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_358, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_354]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_359, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_287, c_0_355]), c_0_292])).
% 0.66/0.84  cnf(c_0_360, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_356, c_0_357])).
% 0.66/0.84  cnf(c_0_361, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_358, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_359])).
% 0.66/0.84  cnf(c_0_362, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_360]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_363, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|~r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_92, c_0_337])).
% 0.66/0.84  cnf(c_0_364, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_361, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_365, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_362])).
% 0.66/0.84  cnf(c_0_366, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_363, c_0_364])).
% 0.66/0.84  cnf(c_0_367, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_345]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_368, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_365, c_0_178])).
% 0.66/0.84  cnf(c_0_369, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_366]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_370, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_367, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_350])).
% 0.66/0.84  cnf(c_0_371, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_278, c_0_368]), c_0_282])).
% 0.66/0.84  cnf(c_0_372, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_369])).
% 0.66/0.84  cnf(c_0_373, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_370, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_374, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_47, c_0_371])).
% 0.66/0.84  cnf(c_0_375, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_354]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_376, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_372, c_0_188])).
% 0.66/0.84  cnf(c_0_377, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_373, c_0_374])).
% 0.66/0.84  cnf(c_0_378, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_375, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_359])).
% 0.66/0.84  cnf(c_0_379, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_287, c_0_376]), c_0_292])).
% 0.66/0.84  cnf(c_0_380, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))), inference(spm,[status(thm)],[c_0_356, c_0_377])).
% 0.66/0.84  cnf(c_0_381, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_378, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_382, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_47, c_0_379])).
% 0.66/0.84  cnf(c_0_383, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_380]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_384, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_381, c_0_382])).
% 0.66/0.84  cnf(c_0_385, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_383])).
% 0.66/0.84  cnf(c_0_386, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))), inference(spm,[status(thm)],[c_0_363, c_0_384])).
% 0.66/0.84  cnf(c_0_387, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk6_2(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_385, c_0_178])).
% 0.66/0.84  cnf(c_0_388, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r2_waybel_9(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_386]), c_0_22]), c_0_20])])).
% 0.66/0.84  cnf(c_0_389, plain, (r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|esk5_2(X1,X2)!=esk6_2(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v1_compts_1(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.66/0.84  cnf(c_0_390, negated_conjecture, (esk6_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_278, c_0_387]), c_0_282])).
% 0.66/0.84  cnf(c_0_391, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|~r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_73, c_0_388])).
% 0.66/0.84  cnf(c_0_392, negated_conjecture, (r2_hidden(X1,k10_yellow_6(esk8_0,esk9_0))|esk5_2(esk8_0,esk9_0)!=k1_waybel_9(esk8_0,esk9_0)|~r3_waybel_9(esk8_0,esk9_0,X1)|~l1_pre_topc(esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_389, c_0_390]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_22])]), c_0_28]), c_0_29])).
% 0.66/0.84  cnf(c_0_393, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)|r3_waybel_9(esk8_0,esk9_0,esk5_2(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_391, c_0_188])).
% 0.66/0.84  cnf(c_0_394, negated_conjecture, (r2_hidden(X1,k10_yellow_6(esk8_0,esk9_0))|esk5_2(esk8_0,esk9_0)!=k1_waybel_9(esk8_0,esk9_0)|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_392, c_0_32]), c_0_17])])).
% 0.66/0.84  cnf(c_0_395, negated_conjecture, (esk5_2(esk8_0,esk9_0)=k1_waybel_9(esk8_0,esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_287, c_0_393]), c_0_292])).
% 0.66/0.84  cnf(c_0_396, negated_conjecture, (r2_hidden(X1,k10_yellow_6(esk8_0,esk9_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_394, c_0_395])])).
% 0.66/0.84  cnf(c_0_397, negated_conjecture, (r2_hidden(k1_waybel_9(esk8_0,esk9_0),k10_yellow_6(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_396, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_398, negated_conjecture, (m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_397])])).
% 0.66/0.84  cnf(c_0_399, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_398]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_400, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_397])])).
% 0.66/0.84  cnf(c_0_401, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_399, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_400])).
% 0.66/0.84  cnf(c_0_402, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_401, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_403, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_398]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_404, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_96, c_0_402])).
% 0.66/0.84  cnf(c_0_405, negated_conjecture, (~r2_waybel_9(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_397])])).
% 0.66/0.84  cnf(c_0_406, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_403, c_0_22]), c_0_23]), c_0_25])]), c_0_28]), c_0_400])).
% 0.66/0.84  cnf(c_0_407, negated_conjecture, (m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_404]), c_0_22]), c_0_20])]), c_0_405])).
% 0.66/0.84  cnf(c_0_408, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_406, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_409, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_47, c_0_407])).
% 0.66/0.84  cnf(c_0_410, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_408, c_0_409])).
% 0.66/0.84  cnf(c_0_411, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_96, c_0_410])).
% 0.66/0.84  cnf(c_0_412, negated_conjecture, (m1_subset_1(esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_411]), c_0_22]), c_0_20])]), c_0_405])).
% 0.66/0.84  cnf(c_0_413, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk2_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_47, c_0_412])).
% 0.66/0.84  cnf(c_0_414, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),k1_waybel_9(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_413])])).
% 0.66/0.84  cnf(c_0_415, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_63, c_0_414])).
% 0.66/0.84  cnf(c_0_416, negated_conjecture, (m1_subset_1(esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_415]), c_0_22]), c_0_20])]), c_0_405])).
% 0.66/0.84  cnf(c_0_417, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))), inference(spm,[status(thm)],[c_0_70, c_0_414])).
% 0.66/0.84  cnf(c_0_418, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk3_4(esk8_0,X2,X1,X1),u1_struct_0(esk8_0))|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_416]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_419, negated_conjecture, (r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_417]), c_0_22]), c_0_20])]), c_0_405])).
% 0.66/0.84  cnf(c_0_420, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|m1_subset_1(esk3_4(esk8_0,esk9_0,X1,X1),u1_struct_0(esk8_0))|~r3_waybel_9(esk8_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_418, c_0_22]), c_0_23]), c_0_25]), c_0_419])]), c_0_28])).
% 0.66/0.84  cnf(c_0_421, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|~r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_92, c_0_414])).
% 0.66/0.84  cnf(c_0_422, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_420, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_423, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|v2_struct_0(X2)|~r3_waybel_9(esk8_0,X2,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,X2,X1,X1)),esk8_0,esk8_0)|~v7_waybel_0(X2)|~v4_orders_2(X2)|~l1_waybel_0(X2,esk8_0)|~r1_lattice3(esk8_0,k2_relset_1(u1_struct_0(X2),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,X2)),esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_416]), c_0_24]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_27]), c_0_17]), c_0_39]), c_0_15])])).
% 0.66/0.84  cnf(c_0_424, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))|m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_421, c_0_422])).
% 0.66/0.84  cnf(c_0_425, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),X1)|~r3_waybel_9(esk8_0,esk9_0,X1)|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,X1,X1)),esk8_0,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_423, c_0_22]), c_0_23]), c_0_25]), c_0_419])]), c_0_28])).
% 0.66/0.84  cnf(c_0_426, negated_conjecture, (m1_subset_1(esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_424]), c_0_22]), c_0_20])]), c_0_405])).
% 0.66/0.84  cnf(c_0_427, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))|~v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_425, c_0_59]), c_0_55])])).
% 0.66/0.84  cnf(c_0_428, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk8_0,esk3_4(esk8_0,esk9_0,k1_waybel_9(esk8_0,esk9_0),k1_waybel_9(esk8_0,esk9_0))),esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_47, c_0_426])).
% 0.66/0.84  cnf(c_0_429, negated_conjecture, (r1_orders_2(esk8_0,esk1_3(esk8_0,k1_waybel_9(esk8_0,esk9_0),k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0))),k1_waybel_9(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_427, c_0_428])])).
% 0.66/0.84  cnf(c_0_430, negated_conjecture, (r2_yellow_0(esk8_0,k2_relset_1(u1_struct_0(esk9_0),u1_struct_0(esk8_0),u1_waybel_0(esk8_0,esk9_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_421, c_0_429])])).
% 0.66/0.84  cnf(c_0_431, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_430]), c_0_22]), c_0_20])]), c_0_405]), ['proof']).
% 0.66/0.84  # SZS output end CNFRefutation
% 0.66/0.84  # Proof object total steps             : 432
% 0.66/0.84  # Proof object clause steps            : 411
% 0.66/0.84  # Proof object formula steps           : 21
% 0.66/0.84  # Proof object conjectures             : 390
% 0.66/0.84  # Proof object clause conjectures      : 387
% 0.66/0.84  # Proof object formula conjectures     : 3
% 0.66/0.84  # Proof object initial clauses used    : 36
% 0.66/0.84  # Proof object initial formulas used   : 10
% 0.66/0.84  # Proof object generating inferences   : 356
% 0.66/0.84  # Proof object simplifying inferences  : 896
% 0.66/0.84  # Training examples: 0 positive, 0 negative
% 0.66/0.84  # Parsed axioms                        : 10
% 0.66/0.84  # Removed by relevancy pruning/SinE    : 0
% 0.66/0.84  # Initial clauses                      : 42
% 0.66/0.84  # Removed in clause preprocessing      : 0
% 0.66/0.84  # Initial clauses in saturation        : 42
% 0.66/0.84  # Processed clauses                    : 1829
% 0.66/0.84  # ...of these trivial                  : 1
% 0.66/0.84  # ...subsumed                          : 290
% 0.66/0.84  # ...remaining for further processing  : 1538
% 0.66/0.84  # Other redundant clauses eliminated   : 6
% 0.66/0.84  # Clauses deleted for lack of memory   : 0
% 0.66/0.84  # Backward-subsumed                    : 816
% 0.66/0.84  # Backward-rewritten                   : 548
% 0.66/0.84  # Generated clauses                    : 3766
% 0.66/0.84  # ...of the previous two non-trivial   : 3724
% 0.66/0.84  # Contextual simplify-reflections      : 126
% 0.66/0.84  # Paramodulations                      : 3758
% 0.66/0.84  # Factorizations                       : 0
% 0.66/0.84  # Equation resolutions                 : 6
% 0.66/0.84  # Propositional unsat checks           : 0
% 0.66/0.84  #    Propositional check models        : 0
% 0.66/0.84  #    Propositional check unsatisfiable : 0
% 0.66/0.84  #    Propositional clauses             : 0
% 0.66/0.84  #    Propositional clauses after purity: 0
% 0.66/0.84  #    Propositional unsat core size     : 0
% 0.66/0.84  #    Propositional preprocessing time  : 0.000
% 0.66/0.84  #    Propositional encoding time       : 0.000
% 0.66/0.84  #    Propositional solver time         : 0.000
% 0.66/0.84  #    Success case prop preproc time    : 0.000
% 0.66/0.84  #    Success case prop encoding time   : 0.000
% 0.66/0.84  #    Success case prop solver time     : 0.000
% 0.66/0.84  # Current number of processed clauses  : 124
% 0.66/0.84  #    Positive orientable unit clauses  : 36
% 0.66/0.84  #    Positive unorientable unit clauses: 0
% 0.66/0.84  #    Negative unit clauses             : 3
% 0.66/0.84  #    Non-unit-clauses                  : 85
% 0.66/0.84  # Current number of unprocessed clauses: 43
% 0.66/0.84  # ...number of literals in the above   : 248
% 0.66/0.84  # Current number of archived formulas  : 0
% 0.66/0.84  # Current number of archived clauses   : 1408
% 0.66/0.84  # Clause-clause subsumption calls (NU) : 178002
% 0.66/0.84  # Rec. Clause-clause subsumption calls : 8006
% 0.66/0.84  # Non-unit clause-clause subsumptions  : 1229
% 0.66/0.84  # Unit Clause-clause subsumption calls : 883
% 0.66/0.84  # Rewrite failures with RHS unbound    : 0
% 0.66/0.84  # BW rewrite match attempts            : 48
% 0.66/0.84  # BW rewrite match successes           : 22
% 0.66/0.84  # Condensation attempts                : 0
% 0.66/0.84  # Condensation successes               : 0
% 0.66/0.84  # Termbank termtop insertions          : 277126
% 0.66/0.84  
% 0.66/0.84  # -------------------------------------------------
% 0.66/0.84  # User time                : 0.493 s
% 0.66/0.84  # System time              : 0.006 s
% 0.66/0.84  # Total time               : 0.499 s
% 0.66/0.84  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
