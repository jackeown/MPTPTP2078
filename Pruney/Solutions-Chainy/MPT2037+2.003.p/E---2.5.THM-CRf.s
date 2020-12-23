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

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   85 (1073 expanded)
%              Number of clauses        :   60 ( 328 expanded)
%              Number of leaves         :   12 ( 261 expanded)
%              Depth                    :   15
%              Number of atoms          :  561 (14792 expanded)
%              Number of equality atoms :   44 ( 780 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   50 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t36_waybel_9,conjecture,(
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

fof(dt_l1_waybel_9,axiom,(
    ! [X1] :
      ( l1_waybel_9(X1)
     => ( l1_pre_topc(X1)
        & l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

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

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(d2_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => k1_waybel_9(X1,X2) = k5_yellow_2(X1,u1_waybel_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_waybel_9)).

fof(dt_u1_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ( v1_funct_1(u1_waybel_0(X1,X2))
        & v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d6_yellow_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_yellow_2(X1,X2) = k2_yellow_0(X1,k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_yellow_2)).

fof(c_0_12,plain,(
    ! [X27,X28,X29,X30] :
      ( ( m1_subset_1(esk2_4(X27,X28,X29,X30),u1_struct_0(X27))
        | X29 != X30
        | ~ v11_waybel_0(X28,X27)
        | ~ r3_waybel_9(X27,X28,X29)
        | r1_lattice3(X27,k2_relset_1(u1_struct_0(X28),u1_struct_0(X27),u1_waybel_0(X27,X28)),X30)
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X28)
        | ~ v4_orders_2(X28)
        | ~ v7_waybel_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | ~ v2_pre_topc(X27)
        | ~ v8_pre_topc(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ v1_lattice3(X27)
        | ~ v2_lattice3(X27)
        | ~ v1_compts_1(X27)
        | ~ l1_waybel_9(X27) )
      & ( ~ v5_pre_topc(k4_waybel_1(X27,esk2_4(X27,X28,X29,X30)),X27,X27)
        | X29 != X30
        | ~ v11_waybel_0(X28,X27)
        | ~ r3_waybel_9(X27,X28,X29)
        | r1_lattice3(X27,k2_relset_1(u1_struct_0(X28),u1_struct_0(X27),u1_waybel_0(X27,X28)),X30)
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X28)
        | ~ v4_orders_2(X28)
        | ~ v7_waybel_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | ~ v2_pre_topc(X27)
        | ~ v8_pre_topc(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ v1_lattice3(X27)
        | ~ v2_lattice3(X27)
        | ~ v1_compts_1(X27)
        | ~ l1_waybel_9(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l51_waybel_9])])])])])])).

fof(c_0_13,negated_conjecture,(
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
    inference(assume_negation,[status(cth)],[t36_waybel_9])).

cnf(c_0_14,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,negated_conjecture,(
    ! [X41] :
      ( v2_pre_topc(esk4_0)
      & v8_pre_topc(esk4_0)
      & v3_orders_2(esk4_0)
      & v4_orders_2(esk4_0)
      & v5_orders_2(esk4_0)
      & v1_lattice3(esk4_0)
      & v2_lattice3(esk4_0)
      & v1_compts_1(esk4_0)
      & l1_waybel_9(esk4_0)
      & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
      & ~ v2_struct_0(esk6_0)
      & v4_orders_2(esk6_0)
      & v7_waybel_0(esk6_0)
      & l1_waybel_0(esk6_0,esk4_0)
      & ( ~ m1_subset_1(X41,u1_struct_0(esk4_0))
        | v5_pre_topc(k4_waybel_1(esk4_0,X41),esk4_0,esk4_0) )
      & v11_waybel_0(esk6_0,esk4_0)
      & r3_waybel_9(esk4_0,esk6_0,esk5_0)
      & esk5_0 != k1_waybel_9(esk4_0,esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).

cnf(c_0_16,plain,
    ( r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)
    | v2_struct_0(X2)
    | m1_subset_1(esk2_4(X1,X2,X3,X3),u1_struct_0(X1))
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ v11_waybel_0(X2,X1)
    | ~ v7_waybel_0(X2)
    | ~ v1_compts_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_9(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( v11_waybel_0(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( v7_waybel_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v1_compts_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v1_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v8_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( l1_waybel_9(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( v2_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( r1_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),X1)
    | m1_subset_1(esk2_4(esk4_0,esk6_0,X1,X1),u1_struct_0(esk4_0))
    | ~ r3_waybel_9(esk4_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( r3_waybel_9(esk4_0,esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_34,plain,(
    ! [X32,X33,X34,X35,X37] :
      ( ( m1_subset_1(esk3_4(X32,X33,X34,X35),u1_struct_0(X32))
        | X34 != X35
        | ~ r3_waybel_9(X32,X33,X34)
        | ~ m1_subset_1(X37,u1_struct_0(X32))
        | ~ r1_lattice3(X32,k2_relset_1(u1_struct_0(X33),u1_struct_0(X32),u1_waybel_0(X32,X33)),X37)
        | r1_orders_2(X32,X37,X35)
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | v2_struct_0(X33)
        | ~ v4_orders_2(X33)
        | ~ v7_waybel_0(X33)
        | ~ l1_waybel_0(X33,X32)
        | ~ v2_pre_topc(X32)
        | ~ v8_pre_topc(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ v1_lattice3(X32)
        | ~ v2_lattice3(X32)
        | ~ v1_compts_1(X32)
        | ~ l1_waybel_9(X32) )
      & ( ~ v5_pre_topc(k4_waybel_1(X32,esk3_4(X32,X33,X34,X35)),X32,X32)
        | X34 != X35
        | ~ r3_waybel_9(X32,X33,X34)
        | ~ m1_subset_1(X37,u1_struct_0(X32))
        | ~ r1_lattice3(X32,k2_relset_1(u1_struct_0(X33),u1_struct_0(X32),u1_waybel_0(X32,X33)),X37)
        | r1_orders_2(X32,X37,X35)
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | v2_struct_0(X33)
        | ~ v4_orders_2(X33)
        | ~ v7_waybel_0(X33)
        | ~ l1_waybel_0(X33,X32)
        | ~ v2_pre_topc(X32)
        | ~ v8_pre_topc(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ v1_lattice3(X32)
        | ~ v2_lattice3(X32)
        | ~ v1_compts_1(X32)
        | ~ l1_waybel_9(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l52_waybel_9])])])])])])).

cnf(c_0_35,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk4_0,X1),esk4_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( r1_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),esk5_0)
    | m1_subset_1(esk2_4(esk4_0,esk6_0,esk5_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

fof(c_0_38,plain,(
    ! [X26] :
      ( ( l1_pre_topc(X26)
        | ~ l1_waybel_9(X26) )
      & ( l1_orders_2(X26)
        | ~ l1_waybel_9(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).

cnf(c_0_39,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_40,plain,(
    ! [X14,X15,X16,X17,X18] :
      ( ( r1_lattice3(X14,X16,X15)
        | X15 != k2_yellow_0(X14,X16)
        | ~ r2_yellow_0(X14,X16)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r1_lattice3(X14,X16,X17)
        | r1_orders_2(X14,X17,X15)
        | X15 != k2_yellow_0(X14,X16)
        | ~ r2_yellow_0(X14,X16)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( X15 = k2_yellow_0(X14,X18)
        | m1_subset_1(esk1_3(X14,X15,X18),u1_struct_0(X14))
        | ~ r1_lattice3(X14,X18,X15)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( r2_yellow_0(X14,X18)
        | m1_subset_1(esk1_3(X14,X15,X18),u1_struct_0(X14))
        | ~ r1_lattice3(X14,X18,X15)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( X15 = k2_yellow_0(X14,X18)
        | r1_lattice3(X14,X18,esk1_3(X14,X15,X18))
        | ~ r1_lattice3(X14,X18,X15)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( r2_yellow_0(X14,X18)
        | r1_lattice3(X14,X18,esk1_3(X14,X15,X18))
        | ~ r1_lattice3(X14,X18,X15)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( X15 = k2_yellow_0(X14,X18)
        | ~ r1_orders_2(X14,esk1_3(X14,X15,X18),X15)
        | ~ r1_lattice3(X14,X18,X15)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( r2_yellow_0(X14,X18)
        | ~ r1_orders_2(X14,esk1_3(X14,X15,X18),X15)
        | ~ r1_lattice3(X14,X18,X15)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_yellow_0])])])])])])).

cnf(c_0_41,plain,
    ( r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)
    | v2_struct_0(X2)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ v11_waybel_0(X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk2_4(X1,X2,X3,X3)),X1,X1)
    | ~ v7_waybel_0(X2)
    | ~ v1_compts_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_9(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk4_0,esk2_4(esk4_0,esk6_0,esk5_0,esk5_0)),esk4_0,esk4_0)
    | r1_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( l1_orders_2(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X4)
    | m1_subset_1(esk3_4(X1,X4,X3,X3),u1_struct_0(X1))
    | ~ r3_waybel_9(X1,X4,X3)
    | ~ v7_waybel_0(X4)
    | ~ v1_compts_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v4_orders_2(X4)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_9(X1)
    | ~ l1_waybel_0(X4,X1)
    | ~ r1_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_lattice3(X2,X3,esk1_3(X2,X1,X3))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r1_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_32]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_33])]),c_0_30])).

cnf(c_0_47,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_26])).

cnf(c_0_48,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | m1_subset_1(esk1_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_49,plain,(
    ! [X13] :
      ( ~ l1_orders_2(X13)
      | ~ v2_lattice3(X13)
      | ~ v2_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk5_0)
    | m1_subset_1(esk3_4(esk4_0,esk6_0,esk5_0,esk5_0),u1_struct_0(esk4_0))
    | ~ r1_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_32]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_33])]),c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( esk5_0 = k2_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))
    | r1_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_28]),c_0_47]),c_0_33])])).

cnf(c_0_52,negated_conjecture,
    ( esk5_0 = k2_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_46]),c_0_28]),c_0_47]),c_0_33])])).

cnf(c_0_53,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_55,negated_conjecture,
    ( esk5_0 = k2_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))
    | r1_orders_2(esk4_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))),esk5_0)
    | m1_subset_1(esk3_4(esk4_0,esk6_0,esk5_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

fof(c_0_56,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ l1_orders_2(X22)
      | ~ l1_waybel_0(X23,X22)
      | k1_waybel_9(X22,X23) = k5_yellow_2(X22,u1_waybel_0(X22,X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_waybel_9])])])])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    | ~ l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_29])).

cnf(c_0_58,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X4)
    | ~ r3_waybel_9(X1,X4,X3)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X4,X3,X3)),X1,X1)
    | ~ v7_waybel_0(X4)
    | ~ v1_compts_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v4_orders_2(X4)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_waybel_9(X1)
    | ~ l1_waybel_0(X4,X1)
    | ~ r1_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( esk5_0 = k2_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))
    | v5_pre_topc(k4_waybel_1(esk4_0,esk3_4(esk4_0,esk6_0,esk5_0,esk5_0)),esk4_0,esk4_0)
    | r1_orders_2(esk4_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_55])).

fof(c_0_60,plain,(
    ! [X20,X21] :
      ( ( v1_funct_1(u1_waybel_0(X20,X21))
        | ~ l1_struct_0(X20)
        | ~ l1_waybel_0(X21,X20) )
      & ( v1_funct_2(u1_waybel_0(X20,X21),u1_struct_0(X21),u1_struct_0(X20))
        | ~ l1_struct_0(X20)
        | ~ l1_waybel_0(X21,X20) )
      & ( m1_subset_1(u1_waybel_0(X20,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))
        | ~ l1_struct_0(X20)
        | ~ l1_waybel_0(X21,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | k1_waybel_9(X1,X2) = k5_yellow_2(X1,u1_waybel_0(X1,X2))
    | ~ l1_orders_2(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_47])])).

cnf(c_0_63,negated_conjecture,
    ( esk5_0 = k2_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))
    | r1_orders_2(esk4_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))),esk5_0)
    | r1_orders_2(esk4_0,X1,esk5_0)
    | ~ r1_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_32]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_33])]),c_0_30])).

cnf(c_0_64,plain,
    ( m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_65,plain,(
    ! [X12] :
      ( ~ l1_orders_2(X12)
      | l1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_66,negated_conjecture,
    ( esk5_0 != k1_waybel_9(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_67,negated_conjecture,
    ( k1_waybel_9(esk4_0,esk6_0) = k5_yellow_2(esk4_0,u1_waybel_0(esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_27]),c_0_47])]),c_0_62])).

cnf(c_0_68,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,esk1_3(X2,X1,X3),X1)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_69,negated_conjecture,
    ( esk5_0 = k2_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))
    | r1_orders_2(esk4_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_51]),c_0_52])).

fof(c_0_70,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | k2_relset_1(X9,X10,X11) = k2_relat_1(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(u1_waybel_0(esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0))))
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_27])).

cnf(c_0_72,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_73,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_74,negated_conjecture,
    ( esk5_0 != k5_yellow_2(esk4_0,u1_waybel_0(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( esk5_0 = k2_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_46]),c_0_28]),c_0_47]),c_0_33])])).

fof(c_0_76,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | ~ l1_orders_2(X24)
      | ~ v1_relat_1(X25)
      | k5_yellow_2(X24,X25) = k2_yellow_0(X24,k2_relat_1(X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_yellow_2])])])])).

cnf(c_0_77,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(u1_waybel_0(esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_47])])).

cnf(c_0_79,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( k5_yellow_2(esk4_0,u1_waybel_0(esk4_0,esk6_0)) != k2_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,plain,
    ( v2_struct_0(X1)
    | k5_yellow_2(X1,X2) = k2_yellow_0(X1,k2_relat_1(X2))
    | ~ l1_orders_2(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( k2_relat_1(u1_waybel_0(esk4_0,esk6_0)) = k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( v1_relat_1(u1_waybel_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_47]),c_0_83])]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:23:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.38  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.030 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(l51_waybel_9, axiom, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((((X3=X4&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X5),X1,X1)))&v11_waybel_0(X2,X1))&r3_waybel_9(X1,X2,X3))=>r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_waybel_9)).
% 0.13/0.38  fof(t36_waybel_9, conjecture, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(((![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X4),X1,X1))&v11_waybel_0(X3,X1))&r3_waybel_9(X1,X3,X2))=>X2=k1_waybel_9(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_waybel_9)).
% 0.13/0.38  fof(l52_waybel_9, axiom, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((X3=X4&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X5),X1,X1)))&r3_waybel_9(X1,X2,X3))=>![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)=>r1_orders_2(X1,X5,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l52_waybel_9)).
% 0.13/0.38  fof(dt_l1_waybel_9, axiom, ![X1]:(l1_waybel_9(X1)=>(l1_pre_topc(X1)&l1_orders_2(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 0.13/0.38  fof(t31_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k2_yellow_0(X1,X3)&r2_yellow_0(X1,X3))=>(r1_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X3,X4)=>r1_orders_2(X1,X4,X2)))))&((r1_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X3,X4)=>r1_orders_2(X1,X4,X2))))=>(X2=k2_yellow_0(X1,X3)&r2_yellow_0(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_yellow_0)).
% 0.13/0.38  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 0.13/0.38  fof(d2_waybel_9, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(l1_waybel_0(X2,X1)=>k1_waybel_9(X1,X2)=k5_yellow_2(X1,u1_waybel_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_waybel_9)).
% 0.13/0.38  fof(dt_u1_waybel_0, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_waybel_0(X2,X1))=>((v1_funct_1(u1_waybel_0(X1,X2))&v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 0.13/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.13/0.38  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.13/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.38  fof(d6_yellow_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(v1_relat_1(X2)=>k5_yellow_2(X1,X2)=k2_yellow_0(X1,k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_yellow_2)).
% 0.13/0.38  fof(c_0_12, plain, ![X27, X28, X29, X30]:((m1_subset_1(esk2_4(X27,X28,X29,X30),u1_struct_0(X27))|X29!=X30|~v11_waybel_0(X28,X27)|~r3_waybel_9(X27,X28,X29)|r1_lattice3(X27,k2_relset_1(u1_struct_0(X28),u1_struct_0(X27),u1_waybel_0(X27,X28)),X30)|~m1_subset_1(X30,u1_struct_0(X27))|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X28)|~v4_orders_2(X28)|~v7_waybel_0(X28)|~l1_waybel_0(X28,X27))|(~v2_pre_topc(X27)|~v8_pre_topc(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~v1_lattice3(X27)|~v2_lattice3(X27)|~v1_compts_1(X27)|~l1_waybel_9(X27)))&(~v5_pre_topc(k4_waybel_1(X27,esk2_4(X27,X28,X29,X30)),X27,X27)|X29!=X30|~v11_waybel_0(X28,X27)|~r3_waybel_9(X27,X28,X29)|r1_lattice3(X27,k2_relset_1(u1_struct_0(X28),u1_struct_0(X27),u1_waybel_0(X27,X28)),X30)|~m1_subset_1(X30,u1_struct_0(X27))|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X28)|~v4_orders_2(X28)|~v7_waybel_0(X28)|~l1_waybel_0(X28,X27))|(~v2_pre_topc(X27)|~v8_pre_topc(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~v1_lattice3(X27)|~v2_lattice3(X27)|~v1_compts_1(X27)|~l1_waybel_9(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l51_waybel_9])])])])])])).
% 0.13/0.38  fof(c_0_13, negated_conjecture, ~(![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(((![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X4),X1,X1))&v11_waybel_0(X3,X1))&r3_waybel_9(X1,X3,X2))=>X2=k1_waybel_9(X1,X3)))))), inference(assume_negation,[status(cth)],[t36_waybel_9])).
% 0.13/0.38  cnf(c_0_14, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X1))|r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)|v2_struct_0(X2)|X3!=X4|~v11_waybel_0(X2,X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_15, negated_conjecture, ![X41]:(((((((((v2_pre_topc(esk4_0)&v8_pre_topc(esk4_0))&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&v1_lattice3(esk4_0))&v2_lattice3(esk4_0))&v1_compts_1(esk4_0))&l1_waybel_9(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&((((~v2_struct_0(esk6_0)&v4_orders_2(esk6_0))&v7_waybel_0(esk6_0))&l1_waybel_0(esk6_0,esk4_0))&((((~m1_subset_1(X41,u1_struct_0(esk4_0))|v5_pre_topc(k4_waybel_1(esk4_0,X41),esk4_0,esk4_0))&v11_waybel_0(esk6_0,esk4_0))&r3_waybel_9(esk4_0,esk6_0,esk5_0))&esk5_0!=k1_waybel_9(esk4_0,esk6_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).
% 0.13/0.38  cnf(c_0_16, plain, (r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)|v2_struct_0(X2)|m1_subset_1(esk2_4(X1,X2,X3,X3),u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v11_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v1_compts_1(X1)|~v1_lattice3(X1)|~v4_orders_2(X2)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X2,X1)|~v5_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (v11_waybel_0(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (v7_waybel_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (v1_compts_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (v1_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (v4_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (v8_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (l1_waybel_9(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (l1_waybel_0(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (v2_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (r1_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),X1)|m1_subset_1(esk2_4(esk4_0,esk6_0,X1,X1),u1_struct_0(esk4_0))|~r3_waybel_9(esk4_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (r3_waybel_9(esk4_0,esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_34, plain, ![X32, X33, X34, X35, X37]:((m1_subset_1(esk3_4(X32,X33,X34,X35),u1_struct_0(X32))|X34!=X35|~r3_waybel_9(X32,X33,X34)|(~m1_subset_1(X37,u1_struct_0(X32))|(~r1_lattice3(X32,k2_relset_1(u1_struct_0(X33),u1_struct_0(X32),u1_waybel_0(X32,X33)),X37)|r1_orders_2(X32,X37,X35)))|~m1_subset_1(X35,u1_struct_0(X32))|~m1_subset_1(X34,u1_struct_0(X32))|(v2_struct_0(X33)|~v4_orders_2(X33)|~v7_waybel_0(X33)|~l1_waybel_0(X33,X32))|(~v2_pre_topc(X32)|~v8_pre_topc(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~v1_lattice3(X32)|~v2_lattice3(X32)|~v1_compts_1(X32)|~l1_waybel_9(X32)))&(~v5_pre_topc(k4_waybel_1(X32,esk3_4(X32,X33,X34,X35)),X32,X32)|X34!=X35|~r3_waybel_9(X32,X33,X34)|(~m1_subset_1(X37,u1_struct_0(X32))|(~r1_lattice3(X32,k2_relset_1(u1_struct_0(X33),u1_struct_0(X32),u1_waybel_0(X32,X33)),X37)|r1_orders_2(X32,X37,X35)))|~m1_subset_1(X35,u1_struct_0(X32))|~m1_subset_1(X34,u1_struct_0(X32))|(v2_struct_0(X33)|~v4_orders_2(X33)|~v7_waybel_0(X33)|~l1_waybel_0(X33,X32))|(~v2_pre_topc(X32)|~v8_pre_topc(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~v1_lattice3(X32)|~v2_lattice3(X32)|~v1_compts_1(X32)|~l1_waybel_9(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l52_waybel_9])])])])])])).
% 0.13/0.38  cnf(c_0_35, plain, (r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)|v2_struct_0(X2)|~v5_pre_topc(k4_waybel_1(X1,esk2_4(X1,X2,X3,X4)),X1,X1)|X3!=X4|~v11_waybel_0(X2,X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk4_0,X1),esk4_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (r1_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),esk5_0)|m1_subset_1(esk2_4(esk4_0,esk6_0,esk5_0,esk5_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.13/0.38  fof(c_0_38, plain, ![X26]:((l1_pre_topc(X26)|~l1_waybel_9(X26))&(l1_orders_2(X26)|~l1_waybel_9(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).
% 0.13/0.38  cnf(c_0_39, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X1))|r1_orders_2(X1,X5,X4)|v2_struct_0(X2)|X3!=X4|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X5,u1_struct_0(X1))|~r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  fof(c_0_40, plain, ![X14, X15, X16, X17, X18]:(((r1_lattice3(X14,X16,X15)|(X15!=k2_yellow_0(X14,X16)|~r2_yellow_0(X14,X16))|~m1_subset_1(X15,u1_struct_0(X14))|(~v5_orders_2(X14)|~l1_orders_2(X14)))&(~m1_subset_1(X17,u1_struct_0(X14))|(~r1_lattice3(X14,X16,X17)|r1_orders_2(X14,X17,X15))|(X15!=k2_yellow_0(X14,X16)|~r2_yellow_0(X14,X16))|~m1_subset_1(X15,u1_struct_0(X14))|(~v5_orders_2(X14)|~l1_orders_2(X14))))&(((X15=k2_yellow_0(X14,X18)|(m1_subset_1(esk1_3(X14,X15,X18),u1_struct_0(X14))|~r1_lattice3(X14,X18,X15))|~m1_subset_1(X15,u1_struct_0(X14))|(~v5_orders_2(X14)|~l1_orders_2(X14)))&(r2_yellow_0(X14,X18)|(m1_subset_1(esk1_3(X14,X15,X18),u1_struct_0(X14))|~r1_lattice3(X14,X18,X15))|~m1_subset_1(X15,u1_struct_0(X14))|(~v5_orders_2(X14)|~l1_orders_2(X14))))&(((X15=k2_yellow_0(X14,X18)|(r1_lattice3(X14,X18,esk1_3(X14,X15,X18))|~r1_lattice3(X14,X18,X15))|~m1_subset_1(X15,u1_struct_0(X14))|(~v5_orders_2(X14)|~l1_orders_2(X14)))&(r2_yellow_0(X14,X18)|(r1_lattice3(X14,X18,esk1_3(X14,X15,X18))|~r1_lattice3(X14,X18,X15))|~m1_subset_1(X15,u1_struct_0(X14))|(~v5_orders_2(X14)|~l1_orders_2(X14))))&((X15=k2_yellow_0(X14,X18)|(~r1_orders_2(X14,esk1_3(X14,X15,X18),X15)|~r1_lattice3(X14,X18,X15))|~m1_subset_1(X15,u1_struct_0(X14))|(~v5_orders_2(X14)|~l1_orders_2(X14)))&(r2_yellow_0(X14,X18)|(~r1_orders_2(X14,esk1_3(X14,X15,X18),X15)|~r1_lattice3(X14,X18,X15))|~m1_subset_1(X15,u1_struct_0(X14))|(~v5_orders_2(X14)|~l1_orders_2(X14))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_yellow_0])])])])])])).
% 0.13/0.38  cnf(c_0_41, plain, (r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~v11_waybel_0(X2,X1)|~v5_pre_topc(k4_waybel_1(X1,esk2_4(X1,X2,X3,X3)),X1,X1)|~v7_waybel_0(X2)|~v1_compts_1(X1)|~v1_lattice3(X1)|~v4_orders_2(X2)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X2,X1)|~v5_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk4_0,esk2_4(esk4_0,esk6_0,esk5_0,esk5_0)),esk4_0,esk4_0)|r1_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.38  cnf(c_0_43, plain, (l1_orders_2(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.38  cnf(c_0_44, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X4)|m1_subset_1(esk3_4(X1,X4,X3,X3),u1_struct_0(X1))|~r3_waybel_9(X1,X4,X3)|~v7_waybel_0(X4)|~v1_compts_1(X1)|~v1_lattice3(X1)|~v4_orders_2(X4)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X4,X1)|~r1_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X2)|~v5_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_45, plain, (X1=k2_yellow_0(X2,X3)|r1_lattice3(X2,X3,esk1_3(X2,X1,X3))|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (r1_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_32]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_33])]), c_0_30])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_26])).
% 0.13/0.38  cnf(c_0_48, plain, (X1=k2_yellow_0(X2,X3)|m1_subset_1(esk1_3(X2,X1,X3),u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.38  fof(c_0_49, plain, ![X13]:(~l1_orders_2(X13)|(~v2_lattice3(X13)|~v2_struct_0(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (r1_orders_2(esk4_0,X1,esk5_0)|m1_subset_1(esk3_4(esk4_0,esk6_0,esk5_0,esk5_0),u1_struct_0(esk4_0))|~r1_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_32]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_33])]), c_0_30])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (esk5_0=k2_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))|r1_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_28]), c_0_47]), c_0_33])])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (esk5_0=k2_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_46]), c_0_28]), c_0_47]), c_0_33])])).
% 0.13/0.38  cnf(c_0_53, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.38  cnf(c_0_54, plain, (r1_orders_2(X1,X5,X4)|v2_struct_0(X2)|~v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X2,X3,X4)),X1,X1)|X3!=X4|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X5,u1_struct_0(X1))|~r1_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (esk5_0=k2_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))|r1_orders_2(esk4_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))),esk5_0)|m1_subset_1(esk3_4(esk4_0,esk6_0,esk5_0,esk5_0),u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.13/0.38  fof(c_0_56, plain, ![X22, X23]:(v2_struct_0(X22)|~l1_orders_2(X22)|(~l1_waybel_0(X23,X22)|k1_waybel_9(X22,X23)=k5_yellow_2(X22,u1_waybel_0(X22,X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_waybel_9])])])])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (~v2_struct_0(esk4_0)|~l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_53, c_0_29])).
% 0.13/0.38  cnf(c_0_58, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X4)|~r3_waybel_9(X1,X4,X3)|~v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X4,X3,X3)),X1,X1)|~v7_waybel_0(X4)|~v1_compts_1(X1)|~v1_lattice3(X1)|~v4_orders_2(X4)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X4,X1)|~r1_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X2)|~v5_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_54])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (esk5_0=k2_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))|v5_pre_topc(k4_waybel_1(esk4_0,esk3_4(esk4_0,esk6_0,esk5_0,esk5_0)),esk4_0,esk4_0)|r1_orders_2(esk4_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))),esk5_0)), inference(spm,[status(thm)],[c_0_36, c_0_55])).
% 0.13/0.38  fof(c_0_60, plain, ![X20, X21]:(((v1_funct_1(u1_waybel_0(X20,X21))|(~l1_struct_0(X20)|~l1_waybel_0(X21,X20)))&(v1_funct_2(u1_waybel_0(X20,X21),u1_struct_0(X21),u1_struct_0(X20))|(~l1_struct_0(X20)|~l1_waybel_0(X21,X20))))&(m1_subset_1(u1_waybel_0(X20,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))|(~l1_struct_0(X20)|~l1_waybel_0(X21,X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).
% 0.13/0.38  cnf(c_0_61, plain, (v2_struct_0(X1)|k1_waybel_9(X1,X2)=k5_yellow_2(X1,u1_waybel_0(X1,X2))|~l1_orders_2(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (~v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_47])])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (esk5_0=k2_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))|r1_orders_2(esk4_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))),esk5_0)|r1_orders_2(esk4_0,X1,esk5_0)|~r1_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_32]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_33])]), c_0_30])).
% 0.13/0.38  cnf(c_0_64, plain, (m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.38  fof(c_0_65, plain, ![X12]:(~l1_orders_2(X12)|l1_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (esk5_0!=k1_waybel_9(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (k1_waybel_9(esk4_0,esk6_0)=k5_yellow_2(esk4_0,u1_waybel_0(esk4_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_27]), c_0_47])]), c_0_62])).
% 0.13/0.38  cnf(c_0_68, plain, (X1=k2_yellow_0(X2,X3)|~r1_orders_2(X2,esk1_3(X2,X1,X3),X1)|~r1_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (esk5_0=k2_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))|r1_orders_2(esk4_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_51]), c_0_52])).
% 0.13/0.38  fof(c_0_70, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|k2_relset_1(X9,X10,X11)=k2_relat_1(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (m1_subset_1(u1_waybel_0(esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0))))|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_64, c_0_27])).
% 0.13/0.38  cnf(c_0_72, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.38  fof(c_0_73, plain, ![X6, X7, X8]:(~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))|v1_relat_1(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.38  cnf(c_0_74, negated_conjecture, (esk5_0!=k5_yellow_2(esk4_0,u1_waybel_0(esk4_0,esk6_0))), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 0.13/0.38  cnf(c_0_75, negated_conjecture, (esk5_0=k2_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_46]), c_0_28]), c_0_47]), c_0_33])])).
% 0.13/0.38  fof(c_0_76, plain, ![X24, X25]:(v2_struct_0(X24)|~l1_orders_2(X24)|(~v1_relat_1(X25)|k5_yellow_2(X24,X25)=k2_yellow_0(X24,k2_relat_1(X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_yellow_2])])])])).
% 0.13/0.38  cnf(c_0_77, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.13/0.38  cnf(c_0_78, negated_conjecture, (m1_subset_1(u1_waybel_0(esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_47])])).
% 0.13/0.38  cnf(c_0_79, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.13/0.38  cnf(c_0_80, negated_conjecture, (k5_yellow_2(esk4_0,u1_waybel_0(esk4_0,esk6_0))!=k2_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.13/0.38  cnf(c_0_81, plain, (v2_struct_0(X1)|k5_yellow_2(X1,X2)=k2_yellow_0(X1,k2_relat_1(X2))|~l1_orders_2(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.13/0.38  cnf(c_0_82, negated_conjecture, (k2_relat_1(u1_waybel_0(esk4_0,esk6_0))=k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.13/0.38  cnf(c_0_83, negated_conjecture, (v1_relat_1(u1_waybel_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_79, c_0_78])).
% 0.13/0.38  cnf(c_0_84, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_47]), c_0_83])]), c_0_62]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 85
% 0.13/0.38  # Proof object clause steps            : 60
% 0.13/0.38  # Proof object formula steps           : 25
% 0.13/0.38  # Proof object conjectures             : 44
% 0.13/0.38  # Proof object clause conjectures      : 41
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 33
% 0.13/0.38  # Proof object initial formulas used   : 12
% 0.13/0.38  # Proof object generating inferences   : 20
% 0.13/0.38  # Proof object simplifying inferences  : 97
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 12
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 41
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 41
% 0.13/0.38  # Processed clauses                    : 123
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 123
% 0.13/0.38  # Other redundant clauses eliminated   : 6
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 3
% 0.13/0.38  # Backward-rewritten                   : 24
% 0.13/0.38  # Generated clauses                    : 51
% 0.13/0.38  # ...of the previous two non-trivial   : 61
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 45
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 6
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
% 0.13/0.38  # Current number of processed clauses  : 49
% 0.13/0.38  #    Positive orientable unit clauses  : 21
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 25
% 0.13/0.38  # Current number of unprocessed clauses: 20
% 0.13/0.38  # ...number of literals in the above   : 55
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 68
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1000
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 129
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.13/0.38  # Unit Clause-clause subsumption calls : 25
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 9
% 0.13/0.38  # BW rewrite match successes           : 8
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6819
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.035 s
% 0.13/0.38  # System time              : 0.008 s
% 0.13/0.38  # Total time               : 0.044 s
% 0.13/0.38  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
