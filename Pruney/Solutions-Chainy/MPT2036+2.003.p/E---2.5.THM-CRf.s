%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:46 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   91 (1274 expanded)
%              Number of clauses        :   64 ( 390 expanded)
%              Number of leaves         :   13 ( 310 expanded)
%              Depth                    :   16
%              Number of atoms          :  595 (17525 expanded)
%              Number of equality atoms :   45 ( 921 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   50 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t35_waybel_9,conjecture,(
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

fof(dt_l1_waybel_9,axiom,(
    ! [X1] :
      ( l1_waybel_9(X1)
     => ( l1_pre_topc(X1)
        & l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(d1_waybel_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => k1_waybel_2(X1,X2) = k4_yellow_2(X1,u1_waybel_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_waybel_2)).

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

fof(dt_u1_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ( v1_funct_1(u1_waybel_0(X1,X2))
        & v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d5_yellow_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_yellow_2(X1,X2) = k1_yellow_0(X1,k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_2)).

fof(c_0_13,plain,(
    ! [X30,X31,X32,X33] :
      ( ( m1_subset_1(esk2_4(X30,X31,X32,X33),u1_struct_0(X30))
        | X32 != X33
        | ~ v10_waybel_0(X31,X30)
        | ~ r3_waybel_9(X30,X31,X32)
        | r2_lattice3(X30,k2_relset_1(u1_struct_0(X31),u1_struct_0(X30),u1_waybel_0(X30,X31)),X33)
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | v2_struct_0(X31)
        | ~ v4_orders_2(X31)
        | ~ v7_waybel_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | ~ v2_pre_topc(X30)
        | ~ v8_pre_topc(X30)
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ v1_lattice3(X30)
        | ~ v2_lattice3(X30)
        | ~ v1_compts_1(X30)
        | ~ l1_waybel_9(X30) )
      & ( ~ v5_pre_topc(k4_waybel_1(X30,esk2_4(X30,X31,X32,X33)),X30,X30)
        | X32 != X33
        | ~ v10_waybel_0(X31,X30)
        | ~ r3_waybel_9(X30,X31,X32)
        | r2_lattice3(X30,k2_relset_1(u1_struct_0(X31),u1_struct_0(X30),u1_waybel_0(X30,X31)),X33)
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | v2_struct_0(X31)
        | ~ v4_orders_2(X31)
        | ~ v7_waybel_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | ~ v2_pre_topc(X30)
        | ~ v8_pre_topc(X30)
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ v1_lattice3(X30)
        | ~ v2_lattice3(X30)
        | ~ v1_compts_1(X30)
        | ~ l1_waybel_9(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l48_waybel_9])])])])])])).

fof(c_0_14,negated_conjecture,(
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
                    & v10_waybel_0(X3,X1)
                    & r3_waybel_9(X1,X3,X2) )
                 => X2 = k1_waybel_2(X1,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t35_waybel_9])).

cnf(c_0_15,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,negated_conjecture,(
    ! [X44] :
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
      & ( ~ m1_subset_1(X44,u1_struct_0(esk4_0))
        | v5_pre_topc(k4_waybel_1(esk4_0,X44),esk4_0,esk4_0) )
      & v10_waybel_0(esk6_0,esk4_0)
      & r3_waybel_9(esk4_0,esk6_0,esk5_0)
      & esk5_0 != k1_waybel_2(esk4_0,esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).

cnf(c_0_17,plain,
    ( r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)
    | v2_struct_0(X2)
    | m1_subset_1(esk2_4(X1,X2,X3,X3),u1_struct_0(X1))
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
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( v10_waybel_0(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( v7_waybel_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_compts_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v2_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v8_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( l1_waybel_9(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( v1_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( r2_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),X1)
    | m1_subset_1(esk2_4(esk4_0,esk6_0,X1,X1),u1_struct_0(esk4_0))
    | ~ r3_waybel_9(esk4_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_33,negated_conjecture,
    ( r3_waybel_9(esk4_0,esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_35,plain,(
    ! [X35,X36,X37,X38,X40] :
      ( ( m1_subset_1(esk3_4(X35,X36,X37,X38),u1_struct_0(X35))
        | X37 != X38
        | ~ r3_waybel_9(X35,X36,X37)
        | ~ m1_subset_1(X40,u1_struct_0(X35))
        | ~ r2_lattice3(X35,k2_relset_1(u1_struct_0(X36),u1_struct_0(X35),u1_waybel_0(X35,X36)),X40)
        | r3_orders_2(X35,X38,X40)
        | ~ m1_subset_1(X38,u1_struct_0(X35))
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | v2_struct_0(X36)
        | ~ v4_orders_2(X36)
        | ~ v7_waybel_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | ~ v2_pre_topc(X35)
        | ~ v8_pre_topc(X35)
        | ~ v3_orders_2(X35)
        | ~ v4_orders_2(X35)
        | ~ v5_orders_2(X35)
        | ~ v1_lattice3(X35)
        | ~ v2_lattice3(X35)
        | ~ v1_compts_1(X35)
        | ~ l1_waybel_9(X35) )
      & ( ~ v5_pre_topc(k4_waybel_1(X35,esk3_4(X35,X36,X37,X38)),X35,X35)
        | X37 != X38
        | ~ r3_waybel_9(X35,X36,X37)
        | ~ m1_subset_1(X40,u1_struct_0(X35))
        | ~ r2_lattice3(X35,k2_relset_1(u1_struct_0(X36),u1_struct_0(X35),u1_waybel_0(X35,X36)),X40)
        | r3_orders_2(X35,X38,X40)
        | ~ m1_subset_1(X38,u1_struct_0(X35))
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | v2_struct_0(X36)
        | ~ v4_orders_2(X36)
        | ~ v7_waybel_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | ~ v2_pre_topc(X35)
        | ~ v8_pre_topc(X35)
        | ~ v3_orders_2(X35)
        | ~ v4_orders_2(X35)
        | ~ v5_orders_2(X35)
        | ~ v1_lattice3(X35)
        | ~ v2_lattice3(X35)
        | ~ v1_compts_1(X35)
        | ~ l1_waybel_9(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l49_waybel_9])])])])])])).

cnf(c_0_36,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk4_0,X1),esk4_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( r2_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),esk5_0)
    | m1_subset_1(esk2_4(esk4_0,esk6_0,esk5_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

fof(c_0_39,plain,(
    ! [X29] :
      ( ( l1_pre_topc(X29)
        | ~ l1_waybel_9(X29) )
      & ( l1_orders_2(X29)
        | ~ l1_waybel_9(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).

cnf(c_0_40,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_41,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( ( r2_lattice3(X17,X19,X18)
        | X18 != k1_yellow_0(X17,X19)
        | ~ r1_yellow_0(X17,X19)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r2_lattice3(X17,X19,X20)
        | r1_orders_2(X17,X18,X20)
        | X18 != k1_yellow_0(X17,X19)
        | ~ r1_yellow_0(X17,X19)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( X18 = k1_yellow_0(X17,X21)
        | m1_subset_1(esk1_3(X17,X18,X21),u1_struct_0(X17))
        | ~ r2_lattice3(X17,X21,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_yellow_0(X17,X21)
        | m1_subset_1(esk1_3(X17,X18,X21),u1_struct_0(X17))
        | ~ r2_lattice3(X17,X21,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( X18 = k1_yellow_0(X17,X21)
        | r2_lattice3(X17,X21,esk1_3(X17,X18,X21))
        | ~ r2_lattice3(X17,X21,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_yellow_0(X17,X21)
        | r2_lattice3(X17,X21,esk1_3(X17,X18,X21))
        | ~ r2_lattice3(X17,X21,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( X18 = k1_yellow_0(X17,X21)
        | ~ r1_orders_2(X17,X18,esk1_3(X17,X18,X21))
        | ~ r2_lattice3(X17,X21,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_yellow_0(X17,X21)
        | ~ r1_orders_2(X17,X18,esk1_3(X17,X18,X21))
        | ~ r2_lattice3(X17,X21,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

cnf(c_0_42,plain,
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
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk4_0,esk2_4(esk4_0,esk6_0,esk5_0,esk5_0)),esk4_0,esk4_0)
    | r2_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( l1_orders_2(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X4)
    | m1_subset_1(esk3_4(X1,X4,X2,X2),u1_struct_0(X1))
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
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r2_lattice3(X2,X3,esk1_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_33]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_34])]),c_0_31])).

cnf(c_0_48,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_26])).

cnf(c_0_49,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | m1_subset_1(esk1_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( r3_orders_2(esk4_0,esk5_0,X1)
    | m1_subset_1(esk3_4(esk4_0,esk6_0,esk5_0,esk5_0),u1_struct_0(esk4_0))
    | ~ r2_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_33]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_34])]),c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( esk5_0 = k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))
    | r2_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_28]),c_0_48]),c_0_34])])).

cnf(c_0_52,negated_conjecture,
    ( esk5_0 = k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))
    | m1_subset_1(esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_47]),c_0_28]),c_0_48]),c_0_34])])).

fof(c_0_53,plain,(
    ! [X16] :
      ( ~ l1_orders_2(X16)
      | ~ v1_lattice3(X16)
      | ~ v2_struct_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

cnf(c_0_54,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_55,negated_conjecture,
    ( esk5_0 = k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))
    | r3_orders_2(esk4_0,esk5_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))))
    | m1_subset_1(esk3_4(esk4_0,esk6_0,esk5_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_56,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,plain,
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
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( esk5_0 = k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))
    | v5_pre_topc(k4_waybel_1(esk4_0,esk3_4(esk4_0,esk6_0,esk5_0,esk5_0)),esk4_0,esk4_0)
    | r3_orders_2(esk4_0,esk5_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_55])).

fof(c_0_59,plain,(
    ! [X25,X26] :
      ( v2_struct_0(X25)
      | ~ l1_orders_2(X25)
      | ~ l1_waybel_0(X26,X25)
      | k1_waybel_2(X25,X26) = k4_yellow_2(X25,u1_waybel_0(X25,X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_waybel_2])])])])).

cnf(c_0_60,negated_conjecture,
    ( ~ l1_orders_2(esk4_0)
    | ~ v2_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_29])).

fof(c_0_61,plain,(
    ! [X13,X14,X15] :
      ( ( ~ r3_orders_2(X13,X14,X15)
        | r1_orders_2(X13,X14,X15)
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ l1_orders_2(X13)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ m1_subset_1(X15,u1_struct_0(X13)) )
      & ( ~ r1_orders_2(X13,X14,X15)
        | r3_orders_2(X13,X14,X15)
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ l1_orders_2(X13)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ m1_subset_1(X15,u1_struct_0(X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_62,negated_conjecture,
    ( esk5_0 = k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))
    | r3_orders_2(esk4_0,esk5_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))))
    | r3_orders_2(esk4_0,esk5_0,X1)
    | ~ r2_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_33]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_34])]),c_0_31])).

fof(c_0_63,plain,(
    ! [X23,X24] :
      ( ( v1_funct_1(u1_waybel_0(X23,X24))
        | ~ l1_struct_0(X23)
        | ~ l1_waybel_0(X24,X23) )
      & ( v1_funct_2(u1_waybel_0(X23,X24),u1_struct_0(X24),u1_struct_0(X23))
        | ~ l1_struct_0(X23)
        | ~ l1_waybel_0(X24,X23) )
      & ( m1_subset_1(u1_waybel_0(X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X23))))
        | ~ l1_struct_0(X23)
        | ~ l1_waybel_0(X24,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).

fof(c_0_64,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(X12)
      | l1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | k1_waybel_2(X1,X2) = k4_yellow_2(X1,u1_waybel_0(X1,X2))
    | ~ l1_orders_2(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_48])])).

cnf(c_0_67,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( esk5_0 = k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))
    | r3_orders_2(esk4_0,esk5_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_51]),c_0_52])).

cnf(c_0_69,plain,
    ( m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,plain,
    ( l1_pre_topc(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_72,negated_conjecture,
    ( esk5_0 != k1_waybel_2(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_73,negated_conjecture,
    ( k1_waybel_2(esk4_0,esk6_0) = k4_yellow_2(esk4_0,u1_waybel_0(esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_27]),c_0_48])]),c_0_66])).

cnf(c_0_74,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,X1,esk1_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_75,negated_conjecture,
    ( esk5_0 = k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))
    | r1_orders_2(esk4_0,esk5_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_48]),c_0_30]),c_0_34])]),c_0_66]),c_0_52])).

fof(c_0_76,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | k2_relset_1(X9,X10,X11) = k2_relat_1(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(u1_waybel_0(esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0))))
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_27])).

cnf(c_0_78,plain,
    ( l1_struct_0(X1)
    | ~ l1_waybel_9(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

fof(c_0_79,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_80,negated_conjecture,
    ( esk5_0 != k4_yellow_2(esk4_0,u1_waybel_0(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( esk5_0 = k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_47]),c_0_28]),c_0_48]),c_0_34])])).

fof(c_0_82,plain,(
    ! [X27,X28] :
      ( v2_struct_0(X27)
      | ~ l1_orders_2(X27)
      | ~ v1_relat_1(X28)
      | k4_yellow_2(X27,X28) = k1_yellow_0(X27,k2_relat_1(X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_yellow_2])])])])).

cnf(c_0_83,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(u1_waybel_0(esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_26])])).

cnf(c_0_85,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( k4_yellow_2(esk4_0,u1_waybel_0(esk4_0,esk6_0)) != k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))) ),
    inference(rw,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_87,plain,
    ( v2_struct_0(X1)
    | k4_yellow_2(X1,X2) = k1_yellow_0(X1,k2_relat_1(X2))
    | ~ l1_orders_2(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( k2_relat_1(u1_waybel_0(esk4_0,esk6_0)) = k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( v1_relat_1(u1_waybel_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_48]),c_0_89])]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.39  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.030 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(l48_waybel_9, axiom, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((((X3=X4&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X5),X1,X1)))&v10_waybel_0(X2,X1))&r3_waybel_9(X1,X2,X3))=>r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l48_waybel_9)).
% 0.13/0.39  fof(t35_waybel_9, conjecture, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(((![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X4),X1,X1))&v10_waybel_0(X3,X1))&r3_waybel_9(X1,X3,X2))=>X2=k1_waybel_2(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_waybel_9)).
% 0.13/0.39  fof(l49_waybel_9, axiom, ![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((X3=X4&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X5),X1,X1)))&r3_waybel_9(X1,X2,X3))=>![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>(r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)=>r3_orders_2(X1,X4,X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_waybel_9)).
% 0.13/0.39  fof(dt_l1_waybel_9, axiom, ![X1]:(l1_waybel_9(X1)=>(l1_pre_topc(X1)&l1_orders_2(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 0.13/0.39  fof(t30_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3))=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))&((r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))=>(X2=k1_yellow_0(X1,X3)&r1_yellow_0(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow_0)).
% 0.13/0.39  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.13/0.39  fof(d1_waybel_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(l1_waybel_0(X2,X1)=>k1_waybel_2(X1,X2)=k4_yellow_2(X1,u1_waybel_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_waybel_2)).
% 0.13/0.39  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.13/0.39  fof(dt_u1_waybel_0, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_waybel_0(X2,X1))=>((v1_funct_1(u1_waybel_0(X1,X2))&v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 0.13/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.13/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.39  fof(d5_yellow_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(v1_relat_1(X2)=>k4_yellow_2(X1,X2)=k1_yellow_0(X1,k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_2)).
% 0.13/0.39  fof(c_0_13, plain, ![X30, X31, X32, X33]:((m1_subset_1(esk2_4(X30,X31,X32,X33),u1_struct_0(X30))|X32!=X33|~v10_waybel_0(X31,X30)|~r3_waybel_9(X30,X31,X32)|r2_lattice3(X30,k2_relset_1(u1_struct_0(X31),u1_struct_0(X30),u1_waybel_0(X30,X31)),X33)|~m1_subset_1(X33,u1_struct_0(X30))|~m1_subset_1(X32,u1_struct_0(X30))|(v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~l1_waybel_0(X31,X30))|(~v2_pre_topc(X30)|~v8_pre_topc(X30)|~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~v1_lattice3(X30)|~v2_lattice3(X30)|~v1_compts_1(X30)|~l1_waybel_9(X30)))&(~v5_pre_topc(k4_waybel_1(X30,esk2_4(X30,X31,X32,X33)),X30,X30)|X32!=X33|~v10_waybel_0(X31,X30)|~r3_waybel_9(X30,X31,X32)|r2_lattice3(X30,k2_relset_1(u1_struct_0(X31),u1_struct_0(X30),u1_waybel_0(X30,X31)),X33)|~m1_subset_1(X33,u1_struct_0(X30))|~m1_subset_1(X32,u1_struct_0(X30))|(v2_struct_0(X31)|~v4_orders_2(X31)|~v7_waybel_0(X31)|~l1_waybel_0(X31,X30))|(~v2_pre_topc(X30)|~v8_pre_topc(X30)|~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~v1_lattice3(X30)|~v2_lattice3(X30)|~v1_compts_1(X30)|~l1_waybel_9(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l48_waybel_9])])])])])])).
% 0.13/0.39  fof(c_0_14, negated_conjecture, ~(![X1]:(((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v1_compts_1(X1))&l1_waybel_9(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((((~(v2_struct_0(X3))&v4_orders_2(X3))&v7_waybel_0(X3))&l1_waybel_0(X3,X1))=>(((![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>v5_pre_topc(k4_waybel_1(X1,X4),X1,X1))&v10_waybel_0(X3,X1))&r3_waybel_9(X1,X3,X2))=>X2=k1_waybel_2(X1,X3)))))), inference(assume_negation,[status(cth)],[t35_waybel_9])).
% 0.13/0.39  cnf(c_0_15, plain, (m1_subset_1(esk2_4(X1,X2,X3,X4),u1_struct_0(X1))|r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)|v2_struct_0(X2)|X3!=X4|~v10_waybel_0(X2,X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  fof(c_0_16, negated_conjecture, ![X44]:(((((((((v2_pre_topc(esk4_0)&v8_pre_topc(esk4_0))&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&v1_lattice3(esk4_0))&v2_lattice3(esk4_0))&v1_compts_1(esk4_0))&l1_waybel_9(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&((((~v2_struct_0(esk6_0)&v4_orders_2(esk6_0))&v7_waybel_0(esk6_0))&l1_waybel_0(esk6_0,esk4_0))&((((~m1_subset_1(X44,u1_struct_0(esk4_0))|v5_pre_topc(k4_waybel_1(esk4_0,X44),esk4_0,esk4_0))&v10_waybel_0(esk6_0,esk4_0))&r3_waybel_9(esk4_0,esk6_0,esk5_0))&esk5_0!=k1_waybel_2(esk4_0,esk6_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).
% 0.13/0.39  cnf(c_0_17, plain, (r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)|v2_struct_0(X2)|m1_subset_1(esk2_4(X1,X2,X3,X3),u1_struct_0(X1))|~r3_waybel_9(X1,X2,X3)|~v10_waybel_0(X2,X1)|~v7_waybel_0(X2)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X2)|~v4_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X2,X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_18, negated_conjecture, (v10_waybel_0(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_19, negated_conjecture, (v7_waybel_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_20, negated_conjecture, (v1_compts_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (v2_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (v4_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_24, negated_conjecture, (v8_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, (l1_waybel_9(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (l1_waybel_0(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (v1_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (r2_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),X1)|m1_subset_1(esk2_4(esk4_0,esk6_0,X1,X1),u1_struct_0(esk4_0))|~r3_waybel_9(esk4_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (r3_waybel_9(esk4_0,esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  fof(c_0_35, plain, ![X35, X36, X37, X38, X40]:((m1_subset_1(esk3_4(X35,X36,X37,X38),u1_struct_0(X35))|X37!=X38|~r3_waybel_9(X35,X36,X37)|(~m1_subset_1(X40,u1_struct_0(X35))|(~r2_lattice3(X35,k2_relset_1(u1_struct_0(X36),u1_struct_0(X35),u1_waybel_0(X35,X36)),X40)|r3_orders_2(X35,X38,X40)))|~m1_subset_1(X38,u1_struct_0(X35))|~m1_subset_1(X37,u1_struct_0(X35))|(v2_struct_0(X36)|~v4_orders_2(X36)|~v7_waybel_0(X36)|~l1_waybel_0(X36,X35))|(~v2_pre_topc(X35)|~v8_pre_topc(X35)|~v3_orders_2(X35)|~v4_orders_2(X35)|~v5_orders_2(X35)|~v1_lattice3(X35)|~v2_lattice3(X35)|~v1_compts_1(X35)|~l1_waybel_9(X35)))&(~v5_pre_topc(k4_waybel_1(X35,esk3_4(X35,X36,X37,X38)),X35,X35)|X37!=X38|~r3_waybel_9(X35,X36,X37)|(~m1_subset_1(X40,u1_struct_0(X35))|(~r2_lattice3(X35,k2_relset_1(u1_struct_0(X36),u1_struct_0(X35),u1_waybel_0(X35,X36)),X40)|r3_orders_2(X35,X38,X40)))|~m1_subset_1(X38,u1_struct_0(X35))|~m1_subset_1(X37,u1_struct_0(X35))|(v2_struct_0(X36)|~v4_orders_2(X36)|~v7_waybel_0(X36)|~l1_waybel_0(X36,X35))|(~v2_pre_topc(X35)|~v8_pre_topc(X35)|~v3_orders_2(X35)|~v4_orders_2(X35)|~v5_orders_2(X35)|~v1_lattice3(X35)|~v2_lattice3(X35)|~v1_compts_1(X35)|~l1_waybel_9(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l49_waybel_9])])])])])])).
% 0.13/0.39  cnf(c_0_36, plain, (r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X4)|v2_struct_0(X2)|~v5_pre_topc(k4_waybel_1(X1,esk2_4(X1,X2,X3,X4)),X1,X1)|X3!=X4|~v10_waybel_0(X2,X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk4_0,X1),esk4_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (r2_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),esk5_0)|m1_subset_1(esk2_4(esk4_0,esk6_0,esk5_0,esk5_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.13/0.39  fof(c_0_39, plain, ![X29]:((l1_pre_topc(X29)|~l1_waybel_9(X29))&(l1_orders_2(X29)|~l1_waybel_9(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).
% 0.13/0.39  cnf(c_0_40, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X1))|r3_orders_2(X1,X4,X5)|v2_struct_0(X2)|X3!=X4|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X5,u1_struct_0(X1))|~r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.39  fof(c_0_41, plain, ![X17, X18, X19, X20, X21]:(((r2_lattice3(X17,X19,X18)|(X18!=k1_yellow_0(X17,X19)|~r1_yellow_0(X17,X19))|~m1_subset_1(X18,u1_struct_0(X17))|(~v5_orders_2(X17)|~l1_orders_2(X17)))&(~m1_subset_1(X20,u1_struct_0(X17))|(~r2_lattice3(X17,X19,X20)|r1_orders_2(X17,X18,X20))|(X18!=k1_yellow_0(X17,X19)|~r1_yellow_0(X17,X19))|~m1_subset_1(X18,u1_struct_0(X17))|(~v5_orders_2(X17)|~l1_orders_2(X17))))&(((X18=k1_yellow_0(X17,X21)|(m1_subset_1(esk1_3(X17,X18,X21),u1_struct_0(X17))|~r2_lattice3(X17,X21,X18))|~m1_subset_1(X18,u1_struct_0(X17))|(~v5_orders_2(X17)|~l1_orders_2(X17)))&(r1_yellow_0(X17,X21)|(m1_subset_1(esk1_3(X17,X18,X21),u1_struct_0(X17))|~r2_lattice3(X17,X21,X18))|~m1_subset_1(X18,u1_struct_0(X17))|(~v5_orders_2(X17)|~l1_orders_2(X17))))&(((X18=k1_yellow_0(X17,X21)|(r2_lattice3(X17,X21,esk1_3(X17,X18,X21))|~r2_lattice3(X17,X21,X18))|~m1_subset_1(X18,u1_struct_0(X17))|(~v5_orders_2(X17)|~l1_orders_2(X17)))&(r1_yellow_0(X17,X21)|(r2_lattice3(X17,X21,esk1_3(X17,X18,X21))|~r2_lattice3(X17,X21,X18))|~m1_subset_1(X18,u1_struct_0(X17))|(~v5_orders_2(X17)|~l1_orders_2(X17))))&((X18=k1_yellow_0(X17,X21)|(~r1_orders_2(X17,X18,esk1_3(X17,X18,X21))|~r2_lattice3(X17,X21,X18))|~m1_subset_1(X18,u1_struct_0(X17))|(~v5_orders_2(X17)|~l1_orders_2(X17)))&(r1_yellow_0(X17,X21)|(~r1_orders_2(X17,X18,esk1_3(X17,X18,X21))|~r2_lattice3(X17,X21,X18))|~m1_subset_1(X18,u1_struct_0(X17))|(~v5_orders_2(X17)|~l1_orders_2(X17))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).
% 0.13/0.39  cnf(c_0_42, plain, (r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X3)|v2_struct_0(X2)|~r3_waybel_9(X1,X2,X3)|~v10_waybel_0(X2,X1)|~v5_pre_topc(k4_waybel_1(X1,esk2_4(X1,X2,X3,X3)),X1,X1)|~v7_waybel_0(X2)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X2)|~v4_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X2,X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_36])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk4_0,esk2_4(esk4_0,esk6_0,esk5_0,esk5_0)),esk4_0,esk4_0)|r2_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.39  cnf(c_0_44, plain, (l1_orders_2(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.39  cnf(c_0_45, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X4)|m1_subset_1(esk3_4(X1,X4,X2,X2),u1_struct_0(X1))|~r3_waybel_9(X1,X4,X2)|~v7_waybel_0(X4)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X4)|~v4_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X4,X1)|~r2_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_40])).
% 0.13/0.39  cnf(c_0_46, plain, (X1=k1_yellow_0(X2,X3)|r2_lattice3(X2,X3,esk1_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (r2_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_33]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_34])]), c_0_31])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (l1_orders_2(esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_26])).
% 0.13/0.39  cnf(c_0_49, plain, (X1=k1_yellow_0(X2,X3)|m1_subset_1(esk1_3(X2,X1,X3),u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (r3_orders_2(esk4_0,esk5_0,X1)|m1_subset_1(esk3_4(esk4_0,esk6_0,esk5_0,esk5_0),u1_struct_0(esk4_0))|~r2_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_33]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_34])]), c_0_31])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (esk5_0=k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))|r2_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_28]), c_0_48]), c_0_34])])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (esk5_0=k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))|m1_subset_1(esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_47]), c_0_28]), c_0_48]), c_0_34])])).
% 0.13/0.39  fof(c_0_53, plain, ![X16]:(~l1_orders_2(X16)|(~v1_lattice3(X16)|~v2_struct_0(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.13/0.39  cnf(c_0_54, plain, (r3_orders_2(X1,X4,X5)|v2_struct_0(X2)|~v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X2,X3,X4)),X1,X1)|X3!=X4|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X5,u1_struct_0(X1))|~r2_lattice3(X1,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)),X5)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v1_compts_1(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (esk5_0=k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))|r3_orders_2(esk4_0,esk5_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))))|m1_subset_1(esk3_4(esk4_0,esk6_0,esk5_0,esk5_0),u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.13/0.39  cnf(c_0_56, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.39  cnf(c_0_57, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X4)|~r3_waybel_9(X1,X4,X2)|~v5_pre_topc(k4_waybel_1(X1,esk3_4(X1,X4,X2,X2)),X1,X1)|~v7_waybel_0(X4)|~v1_compts_1(X1)|~v2_lattice3(X1)|~v4_orders_2(X4)|~v4_orders_2(X1)|~v8_pre_topc(X1)|~v2_pre_topc(X1)|~l1_waybel_9(X1)|~l1_waybel_0(X4,X1)|~r2_lattice3(X1,k2_relset_1(u1_struct_0(X4),u1_struct_0(X1),u1_waybel_0(X1,X4)),X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_54])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, (esk5_0=k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))|v5_pre_topc(k4_waybel_1(esk4_0,esk3_4(esk4_0,esk6_0,esk5_0,esk5_0)),esk4_0,esk4_0)|r3_orders_2(esk4_0,esk5_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))))), inference(spm,[status(thm)],[c_0_37, c_0_55])).
% 0.13/0.39  fof(c_0_59, plain, ![X25, X26]:(v2_struct_0(X25)|~l1_orders_2(X25)|(~l1_waybel_0(X26,X25)|k1_waybel_2(X25,X26)=k4_yellow_2(X25,u1_waybel_0(X25,X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_waybel_2])])])])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (~l1_orders_2(esk4_0)|~v2_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_29])).
% 0.13/0.39  fof(c_0_61, plain, ![X13, X14, X15]:((~r3_orders_2(X13,X14,X15)|r1_orders_2(X13,X14,X15)|(v2_struct_0(X13)|~v3_orders_2(X13)|~l1_orders_2(X13)|~m1_subset_1(X14,u1_struct_0(X13))|~m1_subset_1(X15,u1_struct_0(X13))))&(~r1_orders_2(X13,X14,X15)|r3_orders_2(X13,X14,X15)|(v2_struct_0(X13)|~v3_orders_2(X13)|~l1_orders_2(X13)|~m1_subset_1(X14,u1_struct_0(X13))|~m1_subset_1(X15,u1_struct_0(X13))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (esk5_0=k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))|r3_orders_2(esk4_0,esk5_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))))|r3_orders_2(esk4_0,esk5_0,X1)|~r2_lattice3(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_33]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_34])]), c_0_31])).
% 0.13/0.39  fof(c_0_63, plain, ![X23, X24]:(((v1_funct_1(u1_waybel_0(X23,X24))|(~l1_struct_0(X23)|~l1_waybel_0(X24,X23)))&(v1_funct_2(u1_waybel_0(X23,X24),u1_struct_0(X24),u1_struct_0(X23))|(~l1_struct_0(X23)|~l1_waybel_0(X24,X23))))&(m1_subset_1(u1_waybel_0(X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X23))))|(~l1_struct_0(X23)|~l1_waybel_0(X24,X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).
% 0.13/0.39  fof(c_0_64, plain, ![X12]:(~l1_pre_topc(X12)|l1_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.39  cnf(c_0_65, plain, (v2_struct_0(X1)|k1_waybel_2(X1,X2)=k4_yellow_2(X1,u1_waybel_0(X1,X2))|~l1_orders_2(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.39  cnf(c_0_66, negated_conjecture, (~v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_48])])).
% 0.13/0.39  cnf(c_0_67, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, (esk5_0=k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))|r3_orders_2(esk4_0,esk5_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_51]), c_0_52])).
% 0.13/0.39  cnf(c_0_69, plain, (m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.13/0.39  cnf(c_0_70, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.39  cnf(c_0_71, plain, (l1_pre_topc(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.39  cnf(c_0_72, negated_conjecture, (esk5_0!=k1_waybel_2(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_73, negated_conjecture, (k1_waybel_2(esk4_0,esk6_0)=k4_yellow_2(esk4_0,u1_waybel_0(esk4_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_27]), c_0_48])]), c_0_66])).
% 0.13/0.39  cnf(c_0_74, plain, (X1=k1_yellow_0(X2,X3)|~r1_orders_2(X2,X1,esk1_3(X2,X1,X3))|~r2_lattice3(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.39  cnf(c_0_75, negated_conjecture, (esk5_0=k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))|r1_orders_2(esk4_0,esk5_0,esk1_3(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_48]), c_0_30]), c_0_34])]), c_0_66]), c_0_52])).
% 0.13/0.39  fof(c_0_76, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|k2_relset_1(X9,X10,X11)=k2_relat_1(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.13/0.39  cnf(c_0_77, negated_conjecture, (m1_subset_1(u1_waybel_0(esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0))))|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_69, c_0_27])).
% 0.13/0.39  cnf(c_0_78, plain, (l1_struct_0(X1)|~l1_waybel_9(X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.13/0.39  fof(c_0_79, plain, ![X6, X7, X8]:(~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))|v1_relat_1(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.39  cnf(c_0_80, negated_conjecture, (esk5_0!=k4_yellow_2(esk4_0,u1_waybel_0(esk4_0,esk6_0))), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 0.13/0.39  cnf(c_0_81, negated_conjecture, (esk5_0=k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_47]), c_0_28]), c_0_48]), c_0_34])])).
% 0.13/0.39  fof(c_0_82, plain, ![X27, X28]:(v2_struct_0(X27)|~l1_orders_2(X27)|(~v1_relat_1(X28)|k4_yellow_2(X27,X28)=k1_yellow_0(X27,k2_relat_1(X28)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_yellow_2])])])])).
% 0.13/0.39  cnf(c_0_83, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.13/0.39  cnf(c_0_84, negated_conjecture, (m1_subset_1(u1_waybel_0(esk4_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_26])])).
% 0.13/0.39  cnf(c_0_85, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.13/0.39  cnf(c_0_86, negated_conjecture, (k4_yellow_2(esk4_0,u1_waybel_0(esk4_0,esk6_0))!=k1_yellow_0(esk4_0,k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0)))), inference(rw,[status(thm)],[c_0_80, c_0_81])).
% 0.13/0.39  cnf(c_0_87, plain, (v2_struct_0(X1)|k4_yellow_2(X1,X2)=k1_yellow_0(X1,k2_relat_1(X2))|~l1_orders_2(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.13/0.39  cnf(c_0_88, negated_conjecture, (k2_relat_1(u1_waybel_0(esk4_0,esk6_0))=k2_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.13/0.39  cnf(c_0_89, negated_conjecture, (v1_relat_1(u1_waybel_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_85, c_0_84])).
% 0.13/0.39  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), c_0_48]), c_0_89])]), c_0_66]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 91
% 0.13/0.39  # Proof object clause steps            : 64
% 0.13/0.39  # Proof object formula steps           : 27
% 0.13/0.39  # Proof object conjectures             : 45
% 0.13/0.39  # Proof object clause conjectures      : 42
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 35
% 0.13/0.39  # Proof object initial formulas used   : 13
% 0.13/0.39  # Proof object generating inferences   : 22
% 0.13/0.39  # Proof object simplifying inferences  : 103
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 13
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 43
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 43
% 0.13/0.39  # Processed clauses                    : 133
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 1
% 0.13/0.39  # ...remaining for further processing  : 132
% 0.13/0.39  # Other redundant clauses eliminated   : 6
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 3
% 0.13/0.39  # Backward-rewritten                   : 28
% 0.13/0.39  # Generated clauses                    : 59
% 0.13/0.39  # ...of the previous two non-trivial   : 71
% 0.13/0.39  # Contextual simplify-reflections      : 4
% 0.13/0.39  # Paramodulations                      : 53
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 6
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 52
% 0.13/0.39  #    Positive orientable unit clauses  : 21
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 3
% 0.13/0.39  #    Non-unit-clauses                  : 28
% 0.13/0.39  # Current number of unprocessed clauses: 23
% 0.13/0.39  # ...number of literals in the above   : 60
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 74
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 3642
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 297
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 8
% 0.13/0.39  # Unit Clause-clause subsumption calls : 40
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 10
% 0.13/0.39  # BW rewrite match successes           : 8
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 7449
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.042 s
% 0.13/0.39  # System time              : 0.003 s
% 0.13/0.39  # Total time               : 0.045 s
% 0.13/0.39  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
