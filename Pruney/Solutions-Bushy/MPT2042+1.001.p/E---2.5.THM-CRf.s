%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2042+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:09 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   62 (14239 expanded)
%              Number of clauses        :   55 (3936 expanded)
%              Number of leaves         :    3 (3547 expanded)
%              Depth                    :   22
%              Number of atoms          :  552 (172451 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :  134 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_waybel_9,conjecture,(
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
       => v2_waybel_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_waybel_9)).

fof(t37_waybel_9,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_waybel_9(X1) )
     => ( ( ! [X2] :
              ( ( ~ v2_struct_0(X2)
                & v4_orders_2(X2)
                & v7_waybel_0(X2)
                & l1_waybel_0(X2,X1) )
             => ( v10_waybel_0(X2,X1)
               => ( r1_waybel_9(X1,X2)
                  & r2_hidden(k1_waybel_2(X1,X2),k10_yellow_6(X1,X2)) ) ) )
          & ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => v5_pre_topc(k4_waybel_1(X1,X2),X1,X1) ) )
       => v2_waybel_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_waybel_9)).

fof(t38_waybel_9,axiom,(
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

fof(c_0_3,negated_conjecture,(
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
         => v2_waybel_2(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t41_waybel_9])).

fof(c_0_4,negated_conjecture,(
    ! [X10] :
      ( v2_pre_topc(esk4_0)
      & v8_pre_topc(esk4_0)
      & v3_orders_2(esk4_0)
      & v4_orders_2(esk4_0)
      & v5_orders_2(esk4_0)
      & v1_lattice3(esk4_0)
      & v2_lattice3(esk4_0)
      & v1_compts_1(esk4_0)
      & l1_waybel_9(esk4_0)
      & ( ~ m1_subset_1(X10,u1_struct_0(esk4_0))
        | v5_pre_topc(k4_waybel_1(esk4_0,X10),esk4_0,esk4_0) )
      & ~ v2_waybel_2(esk4_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

fof(c_0_5,plain,(
    ! [X3] :
      ( ( m1_subset_1(esk2_1(X3),u1_struct_0(X3))
        | ~ v2_struct_0(esk1_1(X3))
        | v2_waybel_2(X3)
        | ~ v2_pre_topc(X3)
        | ~ v8_pre_topc(X3)
        | ~ v3_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v5_orders_2(X3)
        | ~ v1_lattice3(X3)
        | ~ v2_lattice3(X3)
        | ~ l1_waybel_9(X3) )
      & ( ~ v5_pre_topc(k4_waybel_1(X3,esk2_1(X3)),X3,X3)
        | ~ v2_struct_0(esk1_1(X3))
        | v2_waybel_2(X3)
        | ~ v2_pre_topc(X3)
        | ~ v8_pre_topc(X3)
        | ~ v3_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v5_orders_2(X3)
        | ~ v1_lattice3(X3)
        | ~ v2_lattice3(X3)
        | ~ l1_waybel_9(X3) )
      & ( m1_subset_1(esk2_1(X3),u1_struct_0(X3))
        | v4_orders_2(esk1_1(X3))
        | v2_waybel_2(X3)
        | ~ v2_pre_topc(X3)
        | ~ v8_pre_topc(X3)
        | ~ v3_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v5_orders_2(X3)
        | ~ v1_lattice3(X3)
        | ~ v2_lattice3(X3)
        | ~ l1_waybel_9(X3) )
      & ( ~ v5_pre_topc(k4_waybel_1(X3,esk2_1(X3)),X3,X3)
        | v4_orders_2(esk1_1(X3))
        | v2_waybel_2(X3)
        | ~ v2_pre_topc(X3)
        | ~ v8_pre_topc(X3)
        | ~ v3_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v5_orders_2(X3)
        | ~ v1_lattice3(X3)
        | ~ v2_lattice3(X3)
        | ~ l1_waybel_9(X3) )
      & ( m1_subset_1(esk2_1(X3),u1_struct_0(X3))
        | v7_waybel_0(esk1_1(X3))
        | v2_waybel_2(X3)
        | ~ v2_pre_topc(X3)
        | ~ v8_pre_topc(X3)
        | ~ v3_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v5_orders_2(X3)
        | ~ v1_lattice3(X3)
        | ~ v2_lattice3(X3)
        | ~ l1_waybel_9(X3) )
      & ( ~ v5_pre_topc(k4_waybel_1(X3,esk2_1(X3)),X3,X3)
        | v7_waybel_0(esk1_1(X3))
        | v2_waybel_2(X3)
        | ~ v2_pre_topc(X3)
        | ~ v8_pre_topc(X3)
        | ~ v3_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v5_orders_2(X3)
        | ~ v1_lattice3(X3)
        | ~ v2_lattice3(X3)
        | ~ l1_waybel_9(X3) )
      & ( m1_subset_1(esk2_1(X3),u1_struct_0(X3))
        | l1_waybel_0(esk1_1(X3),X3)
        | v2_waybel_2(X3)
        | ~ v2_pre_topc(X3)
        | ~ v8_pre_topc(X3)
        | ~ v3_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v5_orders_2(X3)
        | ~ v1_lattice3(X3)
        | ~ v2_lattice3(X3)
        | ~ l1_waybel_9(X3) )
      & ( ~ v5_pre_topc(k4_waybel_1(X3,esk2_1(X3)),X3,X3)
        | l1_waybel_0(esk1_1(X3),X3)
        | v2_waybel_2(X3)
        | ~ v2_pre_topc(X3)
        | ~ v8_pre_topc(X3)
        | ~ v3_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v5_orders_2(X3)
        | ~ v1_lattice3(X3)
        | ~ v2_lattice3(X3)
        | ~ l1_waybel_9(X3) )
      & ( m1_subset_1(esk2_1(X3),u1_struct_0(X3))
        | v10_waybel_0(esk1_1(X3),X3)
        | v2_waybel_2(X3)
        | ~ v2_pre_topc(X3)
        | ~ v8_pre_topc(X3)
        | ~ v3_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v5_orders_2(X3)
        | ~ v1_lattice3(X3)
        | ~ v2_lattice3(X3)
        | ~ l1_waybel_9(X3) )
      & ( ~ v5_pre_topc(k4_waybel_1(X3,esk2_1(X3)),X3,X3)
        | v10_waybel_0(esk1_1(X3),X3)
        | v2_waybel_2(X3)
        | ~ v2_pre_topc(X3)
        | ~ v8_pre_topc(X3)
        | ~ v3_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v5_orders_2(X3)
        | ~ v1_lattice3(X3)
        | ~ v2_lattice3(X3)
        | ~ l1_waybel_9(X3) )
      & ( m1_subset_1(esk2_1(X3),u1_struct_0(X3))
        | ~ r1_waybel_9(X3,esk1_1(X3))
        | ~ r2_hidden(k1_waybel_2(X3,esk1_1(X3)),k10_yellow_6(X3,esk1_1(X3)))
        | v2_waybel_2(X3)
        | ~ v2_pre_topc(X3)
        | ~ v8_pre_topc(X3)
        | ~ v3_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v5_orders_2(X3)
        | ~ v1_lattice3(X3)
        | ~ v2_lattice3(X3)
        | ~ l1_waybel_9(X3) )
      & ( ~ v5_pre_topc(k4_waybel_1(X3,esk2_1(X3)),X3,X3)
        | ~ r1_waybel_9(X3,esk1_1(X3))
        | ~ r2_hidden(k1_waybel_2(X3,esk1_1(X3)),k10_yellow_6(X3,esk1_1(X3)))
        | v2_waybel_2(X3)
        | ~ v2_pre_topc(X3)
        | ~ v8_pre_topc(X3)
        | ~ v3_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v5_orders_2(X3)
        | ~ v1_lattice3(X3)
        | ~ v2_lattice3(X3)
        | ~ l1_waybel_9(X3) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_waybel_9])])])])])).

cnf(c_0_6,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk4_0,X1),esk4_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | v10_waybel_0(esk1_1(X1),X1)
    | v2_waybel_2(X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( l1_waybel_9(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( v2_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( v1_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( v8_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_waybel_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | l1_waybel_0(esk1_1(X1),X1)
    | v2_waybel_2(X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | v7_waybel_0(esk1_1(X1))
    | v2_waybel_2(X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | v4_orders_2(esk1_1(X1))
    | v2_waybel_2(X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_20,plain,(
    ! [X6,X8] :
      ( ( r1_waybel_9(X6,X8)
        | ~ v10_waybel_0(X8,X6)
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ v7_waybel_0(X8)
        | ~ l1_waybel_0(X8,X6)
        | m1_subset_1(esk3_1(X6),u1_struct_0(X6))
        | ~ v2_pre_topc(X6)
        | ~ v8_pre_topc(X6)
        | ~ v3_orders_2(X6)
        | ~ v4_orders_2(X6)
        | ~ v5_orders_2(X6)
        | ~ v1_lattice3(X6)
        | ~ v2_lattice3(X6)
        | ~ v1_compts_1(X6)
        | ~ l1_waybel_9(X6) )
      & ( r2_hidden(k1_waybel_2(X6,X8),k10_yellow_6(X6,X8))
        | ~ v10_waybel_0(X8,X6)
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ v7_waybel_0(X8)
        | ~ l1_waybel_0(X8,X6)
        | m1_subset_1(esk3_1(X6),u1_struct_0(X6))
        | ~ v2_pre_topc(X6)
        | ~ v8_pre_topc(X6)
        | ~ v3_orders_2(X6)
        | ~ v4_orders_2(X6)
        | ~ v5_orders_2(X6)
        | ~ v1_lattice3(X6)
        | ~ v2_lattice3(X6)
        | ~ v1_compts_1(X6)
        | ~ l1_waybel_9(X6) )
      & ( r1_waybel_9(X6,X8)
        | ~ v10_waybel_0(X8,X6)
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ v7_waybel_0(X8)
        | ~ l1_waybel_0(X8,X6)
        | ~ v5_pre_topc(k4_waybel_1(X6,esk3_1(X6)),X6,X6)
        | ~ v2_pre_topc(X6)
        | ~ v8_pre_topc(X6)
        | ~ v3_orders_2(X6)
        | ~ v4_orders_2(X6)
        | ~ v5_orders_2(X6)
        | ~ v1_lattice3(X6)
        | ~ v2_lattice3(X6)
        | ~ v1_compts_1(X6)
        | ~ l1_waybel_9(X6) )
      & ( r2_hidden(k1_waybel_2(X6,X8),k10_yellow_6(X6,X8))
        | ~ v10_waybel_0(X8,X6)
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ v7_waybel_0(X8)
        | ~ l1_waybel_0(X8,X6)
        | ~ v5_pre_topc(k4_waybel_1(X6,esk3_1(X6)),X6,X6)
        | ~ v2_pre_topc(X6)
        | ~ v8_pre_topc(X6)
        | ~ v3_orders_2(X6)
        | ~ v4_orders_2(X6)
        | ~ v5_orders_2(X6)
        | ~ v1_lattice3(X6)
        | ~ v2_lattice3(X6)
        | ~ v1_compts_1(X6)
        | ~ l1_waybel_9(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_waybel_9])])])])])])).

cnf(c_0_21,plain,
    ( v10_waybel_0(esk1_1(X1),X1)
    | v2_waybel_2(X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk2_1(X1)),X1,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk4_0,esk2_1(esk4_0)),esk4_0,esk4_0)
    | v10_waybel_0(esk1_1(esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_23,plain,
    ( l1_waybel_0(esk1_1(X1),X1)
    | v2_waybel_2(X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk2_1(X1)),X1,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk4_0,esk2_1(esk4_0)),esk4_0,esk4_0)
    | l1_waybel_0(esk1_1(esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_17]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_25,plain,
    ( v7_waybel_0(esk1_1(X1))
    | v2_waybel_2(X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk2_1(X1)),X1,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_26,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk4_0,esk2_1(esk4_0)),esk4_0,esk4_0)
    | v7_waybel_0(esk1_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_18]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_27,plain,
    ( v4_orders_2(esk1_1(X1))
    | v2_waybel_2(X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk2_1(X1)),X1,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_28,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk4_0,esk2_1(esk4_0)),esk4_0,esk4_0)
    | v4_orders_2(esk1_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_19]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_29,plain,
    ( r1_waybel_9(X1,X2)
    | v2_struct_0(X2)
    | m1_subset_1(esk3_1(X1),u1_struct_0(X1))
    | ~ v10_waybel_0(X2,X1)
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
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( v10_waybel_0(esk1_1(esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( v1_compts_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_32,negated_conjecture,
    ( l1_waybel_0(esk1_1(esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( v7_waybel_0(esk1_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( v4_orders_2(esk1_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk3_1(esk4_0),u1_struct_0(esk4_0))
    | r1_waybel_9(esk4_0,esk1_1(esk4_0))
    | v2_struct_0(esk1_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_34]),c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_36,plain,
    ( r1_waybel_9(X1,X2)
    | v2_struct_0(X2)
    | ~ v10_waybel_0(X2,X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk3_1(X1)),X1,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk4_0,esk3_1(esk4_0)),esk4_0,esk4_0)
    | r1_waybel_9(esk4_0,esk1_1(esk4_0))
    | v2_struct_0(esk1_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_6,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( r1_waybel_9(esk4_0,esk1_1(esk4_0))
    | r1_waybel_9(esk4_0,X1)
    | v2_struct_0(esk1_1(esk4_0))
    | v2_struct_0(X1)
    | ~ v10_waybel_0(X1,esk4_0)
    | ~ l1_waybel_0(X1,esk4_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_31]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_39,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | v2_waybel_2(X1)
    | ~ r1_waybel_9(X1,esk1_1(X1))
    | ~ r2_hidden(k1_waybel_2(X1,esk1_1(X1)),k10_yellow_6(X1,esk1_1(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_40,negated_conjecture,
    ( r1_waybel_9(esk4_0,esk1_1(esk4_0))
    | v2_struct_0(esk1_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_30]),c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_41,plain,
    ( r2_hidden(k1_waybel_2(X1,X2),k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | m1_subset_1(esk3_1(X1),u1_struct_0(X1))
    | ~ v10_waybel_0(X2,X1)
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
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk2_1(esk4_0),u1_struct_0(esk4_0))
    | v2_struct_0(esk1_1(esk4_0))
    | ~ r2_hidden(k1_waybel_2(esk4_0,esk1_1(esk4_0)),k10_yellow_6(esk4_0,esk1_1(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk3_1(esk4_0),u1_struct_0(esk4_0))
    | r2_hidden(k1_waybel_2(esk4_0,esk1_1(esk4_0)),k10_yellow_6(esk4_0,esk1_1(esk4_0)))
    | v2_struct_0(esk1_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_34]),c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk3_1(esk4_0),u1_struct_0(esk4_0))
    | m1_subset_1(esk2_1(esk4_0),u1_struct_0(esk4_0))
    | v2_struct_0(esk1_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_45,plain,
    ( r2_hidden(k1_waybel_2(X1,X2),k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | ~ v10_waybel_0(X2,X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk3_1(X1)),X1,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk4_0,esk3_1(esk4_0)),esk4_0,esk4_0)
    | m1_subset_1(esk2_1(esk4_0),u1_struct_0(esk4_0))
    | v2_struct_0(esk1_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_6,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk2_1(esk4_0),u1_struct_0(esk4_0))
    | r2_hidden(k1_waybel_2(esk4_0,X1),k10_yellow_6(esk4_0,X1))
    | v2_struct_0(esk1_1(esk4_0))
    | v2_struct_0(X1)
    | ~ v10_waybel_0(X1,esk4_0)
    | ~ l1_waybel_0(X1,esk4_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_31]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_48,plain,
    ( v2_waybel_2(X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk2_1(X1)),X1,X1)
    | ~ r1_waybel_9(X1,esk1_1(X1))
    | ~ r2_hidden(k1_waybel_2(X1,esk1_1(X1)),k10_yellow_6(X1,esk1_1(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk2_1(esk4_0),u1_struct_0(esk4_0))
    | v2_struct_0(esk1_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_30]),c_0_32]),c_0_33]),c_0_34])]),c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( v2_struct_0(esk1_1(esk4_0))
    | ~ v5_pre_topc(k4_waybel_1(esk4_0,esk2_1(esk4_0)),esk4_0,esk4_0)
    | ~ r2_hidden(k1_waybel_2(esk4_0,esk1_1(esk4_0)),k10_yellow_6(esk4_0,esk1_1(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_40]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_51,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk4_0,esk2_1(esk4_0)),esk4_0,esk4_0)
    | v2_struct_0(esk1_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_6,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( v2_struct_0(esk1_1(esk4_0))
    | ~ r2_hidden(k1_waybel_2(esk4_0,esk1_1(esk4_0)),k10_yellow_6(esk4_0,esk1_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk3_1(esk4_0),u1_struct_0(esk4_0))
    | v2_struct_0(esk1_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk4_0,esk3_1(esk4_0)),esk4_0,esk4_0)
    | v2_struct_0(esk1_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_6,c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k1_waybel_2(esk4_0,X1),k10_yellow_6(esk4_0,X1))
    | v2_struct_0(esk1_1(esk4_0))
    | v2_struct_0(X1)
    | ~ v10_waybel_0(X1,esk4_0)
    | ~ l1_waybel_0(X1,esk4_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_54]),c_0_31]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_56,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | v2_waybel_2(X1)
    | ~ v2_struct_0(esk1_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(esk1_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_30]),c_0_32]),c_0_33]),c_0_34])]),c_0_52])).

cnf(c_0_58,plain,
    ( v2_waybel_2(X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk2_1(X1)),X1,X1)
    | ~ v2_struct_0(esk1_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk2_1(esk4_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_60,negated_conjecture,
    ( ~ v5_pre_topc(k4_waybel_1(esk4_0,esk2_1(esk4_0)),esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_57]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_59]),c_0_60]),
    [proof]).

%------------------------------------------------------------------------------
