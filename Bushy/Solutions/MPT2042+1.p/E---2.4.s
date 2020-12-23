%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_9__t41_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:10 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   57 (3580 expanded)
%              Number of clauses        :   50 ( 990 expanded)
%              Number of leaves         :    3 ( 899 expanded)
%              Depth                    :   10
%              Number of atoms          :  556 (46285 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :  134 (   6 average)
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
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',t41_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',t37_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/waybel_9__t41_waybel_9.p',t38_waybel_9)).

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

fof(c_0_4,plain,(
    ! [X37] :
      ( ( m1_subset_1(esk9_1(X37),u1_struct_0(X37))
        | ~ v2_struct_0(esk8_1(X37))
        | v2_waybel_2(X37)
        | ~ v2_pre_topc(X37)
        | ~ v8_pre_topc(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_waybel_9(X37) )
      & ( ~ v5_pre_topc(k4_waybel_1(X37,esk9_1(X37)),X37,X37)
        | ~ v2_struct_0(esk8_1(X37))
        | v2_waybel_2(X37)
        | ~ v2_pre_topc(X37)
        | ~ v8_pre_topc(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_waybel_9(X37) )
      & ( m1_subset_1(esk9_1(X37),u1_struct_0(X37))
        | v4_orders_2(esk8_1(X37))
        | v2_waybel_2(X37)
        | ~ v2_pre_topc(X37)
        | ~ v8_pre_topc(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_waybel_9(X37) )
      & ( ~ v5_pre_topc(k4_waybel_1(X37,esk9_1(X37)),X37,X37)
        | v4_orders_2(esk8_1(X37))
        | v2_waybel_2(X37)
        | ~ v2_pre_topc(X37)
        | ~ v8_pre_topc(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_waybel_9(X37) )
      & ( m1_subset_1(esk9_1(X37),u1_struct_0(X37))
        | v7_waybel_0(esk8_1(X37))
        | v2_waybel_2(X37)
        | ~ v2_pre_topc(X37)
        | ~ v8_pre_topc(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_waybel_9(X37) )
      & ( ~ v5_pre_topc(k4_waybel_1(X37,esk9_1(X37)),X37,X37)
        | v7_waybel_0(esk8_1(X37))
        | v2_waybel_2(X37)
        | ~ v2_pre_topc(X37)
        | ~ v8_pre_topc(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_waybel_9(X37) )
      & ( m1_subset_1(esk9_1(X37),u1_struct_0(X37))
        | l1_waybel_0(esk8_1(X37),X37)
        | v2_waybel_2(X37)
        | ~ v2_pre_topc(X37)
        | ~ v8_pre_topc(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_waybel_9(X37) )
      & ( ~ v5_pre_topc(k4_waybel_1(X37,esk9_1(X37)),X37,X37)
        | l1_waybel_0(esk8_1(X37),X37)
        | v2_waybel_2(X37)
        | ~ v2_pre_topc(X37)
        | ~ v8_pre_topc(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_waybel_9(X37) )
      & ( m1_subset_1(esk9_1(X37),u1_struct_0(X37))
        | v10_waybel_0(esk8_1(X37),X37)
        | v2_waybel_2(X37)
        | ~ v2_pre_topc(X37)
        | ~ v8_pre_topc(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_waybel_9(X37) )
      & ( ~ v5_pre_topc(k4_waybel_1(X37,esk9_1(X37)),X37,X37)
        | v10_waybel_0(esk8_1(X37),X37)
        | v2_waybel_2(X37)
        | ~ v2_pre_topc(X37)
        | ~ v8_pre_topc(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_waybel_9(X37) )
      & ( m1_subset_1(esk9_1(X37),u1_struct_0(X37))
        | ~ r1_waybel_9(X37,esk8_1(X37))
        | ~ r2_hidden(k1_waybel_2(X37,esk8_1(X37)),k10_yellow_6(X37,esk8_1(X37)))
        | v2_waybel_2(X37)
        | ~ v2_pre_topc(X37)
        | ~ v8_pre_topc(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_waybel_9(X37) )
      & ( ~ v5_pre_topc(k4_waybel_1(X37,esk9_1(X37)),X37,X37)
        | ~ r1_waybel_9(X37,esk8_1(X37))
        | ~ r2_hidden(k1_waybel_2(X37,esk8_1(X37)),k10_yellow_6(X37,esk8_1(X37)))
        | v2_waybel_2(X37)
        | ~ v2_pre_topc(X37)
        | ~ v8_pre_topc(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ v1_lattice3(X37)
        | ~ v2_lattice3(X37)
        | ~ l1_waybel_9(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_waybel_9])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X5] :
      ( v2_pre_topc(esk1_0)
      & v8_pre_topc(esk1_0)
      & v3_orders_2(esk1_0)
      & v4_orders_2(esk1_0)
      & v5_orders_2(esk1_0)
      & v1_lattice3(esk1_0)
      & v2_lattice3(esk1_0)
      & v1_compts_1(esk1_0)
      & l1_waybel_9(esk1_0)
      & ( ~ m1_subset_1(X5,u1_struct_0(esk1_0))
        | v5_pre_topc(k4_waybel_1(esk1_0,X5),esk1_0,esk1_0) )
      & ~ v2_waybel_2(esk1_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

cnf(c_0_6,plain,
    ( v10_waybel_0(esk8_1(X1),X1)
    | v2_waybel_2(X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk9_1(X1)),X1,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk1_0,X1),esk1_0,esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( l1_waybel_9(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v1_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( v8_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_waybel_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( v7_waybel_0(esk8_1(X1))
    | v2_waybel_2(X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk9_1(X1)),X1,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,plain,
    ( l1_waybel_0(esk8_1(X1),X1)
    | v2_waybel_2(X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk9_1(X1)),X1,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,plain,
    ( v4_orders_2(esk8_1(X1))
    | v2_waybel_2(X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk9_1(X1)),X1,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,plain,
    ( v2_waybel_2(X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk9_1(X1)),X1,X1)
    | ~ v2_struct_0(esk8_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_21,plain,(
    ! [X40,X42] :
      ( ( r1_waybel_9(X40,X42)
        | ~ v10_waybel_0(X42,X40)
        | v2_struct_0(X42)
        | ~ v4_orders_2(X42)
        | ~ v7_waybel_0(X42)
        | ~ l1_waybel_0(X42,X40)
        | m1_subset_1(esk10_1(X40),u1_struct_0(X40))
        | ~ v2_pre_topc(X40)
        | ~ v8_pre_topc(X40)
        | ~ v3_orders_2(X40)
        | ~ v4_orders_2(X40)
        | ~ v5_orders_2(X40)
        | ~ v1_lattice3(X40)
        | ~ v2_lattice3(X40)
        | ~ v1_compts_1(X40)
        | ~ l1_waybel_9(X40) )
      & ( r2_hidden(k1_waybel_2(X40,X42),k10_yellow_6(X40,X42))
        | ~ v10_waybel_0(X42,X40)
        | v2_struct_0(X42)
        | ~ v4_orders_2(X42)
        | ~ v7_waybel_0(X42)
        | ~ l1_waybel_0(X42,X40)
        | m1_subset_1(esk10_1(X40),u1_struct_0(X40))
        | ~ v2_pre_topc(X40)
        | ~ v8_pre_topc(X40)
        | ~ v3_orders_2(X40)
        | ~ v4_orders_2(X40)
        | ~ v5_orders_2(X40)
        | ~ v1_lattice3(X40)
        | ~ v2_lattice3(X40)
        | ~ v1_compts_1(X40)
        | ~ l1_waybel_9(X40) )
      & ( r1_waybel_9(X40,X42)
        | ~ v10_waybel_0(X42,X40)
        | v2_struct_0(X42)
        | ~ v4_orders_2(X42)
        | ~ v7_waybel_0(X42)
        | ~ l1_waybel_0(X42,X40)
        | ~ v5_pre_topc(k4_waybel_1(X40,esk10_1(X40)),X40,X40)
        | ~ v2_pre_topc(X40)
        | ~ v8_pre_topc(X40)
        | ~ v3_orders_2(X40)
        | ~ v4_orders_2(X40)
        | ~ v5_orders_2(X40)
        | ~ v1_lattice3(X40)
        | ~ v2_lattice3(X40)
        | ~ v1_compts_1(X40)
        | ~ l1_waybel_9(X40) )
      & ( r2_hidden(k1_waybel_2(X40,X42),k10_yellow_6(X40,X42))
        | ~ v10_waybel_0(X42,X40)
        | v2_struct_0(X42)
        | ~ v4_orders_2(X42)
        | ~ v7_waybel_0(X42)
        | ~ l1_waybel_0(X42,X40)
        | ~ v5_pre_topc(k4_waybel_1(X40,esk10_1(X40)),X40,X40)
        | ~ v2_pre_topc(X40)
        | ~ v8_pre_topc(X40)
        | ~ v3_orders_2(X40)
        | ~ v4_orders_2(X40)
        | ~ v5_orders_2(X40)
        | ~ v1_lattice3(X40)
        | ~ v2_lattice3(X40)
        | ~ v1_compts_1(X40)
        | ~ l1_waybel_9(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_waybel_9])])])])])])).

cnf(c_0_22,negated_conjecture,
    ( v10_waybel_0(esk8_1(esk1_0),esk1_0)
    | ~ m1_subset_1(esk9_1(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk9_1(X1),u1_struct_0(X1))
    | v10_waybel_0(esk8_1(X1),X1)
    | v2_waybel_2(X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk1_0))
    | ~ m1_subset_1(esk9_1(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk9_1(X1),u1_struct_0(X1))
    | v7_waybel_0(esk8_1(X1))
    | v2_waybel_2(X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_26,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk1_0),esk1_0)
    | ~ m1_subset_1(esk9_1(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk9_1(X1),u1_struct_0(X1))
    | l1_waybel_0(esk8_1(X1),X1)
    | v2_waybel_2(X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_28,negated_conjecture,
    ( v4_orders_2(esk8_1(esk1_0))
    | ~ m1_subset_1(esk9_1(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk9_1(X1),u1_struct_0(X1))
    | v4_orders_2(esk8_1(X1))
    | v2_waybel_2(X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk8_1(esk1_0))
    | ~ m1_subset_1(esk9_1(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk9_1(X1),u1_struct_0(X1))
    | v2_waybel_2(X1)
    | ~ v2_struct_0(esk8_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_32,plain,
    ( r2_hidden(k1_waybel_2(X1,X2),k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | ~ v10_waybel_0(X2,X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk10_1(X1)),X1,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_34,plain,
    ( v2_waybel_2(X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk9_1(X1)),X1,X1)
    | ~ r1_waybel_9(X1,esk8_1(X1))
    | ~ r2_hidden(k1_waybel_2(X1,esk8_1(X1)),k10_yellow_6(X1,esk8_1(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_35,plain,
    ( r2_hidden(k1_waybel_2(X1,X2),k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | m1_subset_1(esk10_1(X1),u1_struct_0(X1))
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( r1_waybel_9(X1,X2)
    | v2_struct_0(X2)
    | m1_subset_1(esk10_1(X1),u1_struct_0(X1))
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( v10_waybel_0(esk8_1(esk1_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( v7_waybel_0(esk8_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_39,negated_conjecture,
    ( l1_waybel_0(esk8_1(esk1_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( v4_orders_2(esk8_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk8_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(k1_waybel_2(esk1_0,X1),k10_yellow_6(esk1_0,X1))
    | ~ v10_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ m1_subset_1(esk10_1(esk1_0),u1_struct_0(esk1_0))
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_7]),c_0_8]),c_0_33]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_43,plain,
    ( m1_subset_1(esk9_1(X1),u1_struct_0(X1))
    | v2_waybel_2(X1)
    | ~ r1_waybel_9(X1,esk8_1(X1))
    | ~ r2_hidden(k1_waybel_2(X1,esk8_1(X1)),k10_yellow_6(X1,esk8_1(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_44,plain,
    ( v2_waybel_2(X1)
    | m1_subset_1(esk10_1(X1),u1_struct_0(X1))
    | ~ r1_waybel_9(X1,esk8_1(X1))
    | ~ v5_pre_topc(k4_waybel_1(X1,esk9_1(X1)),X1,X1)
    | ~ l1_waybel_9(X1)
    | ~ v1_compts_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_19]),c_0_18]),c_0_17]),c_0_6]),c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( r1_waybel_9(esk1_0,esk8_1(esk1_0))
    | m1_subset_1(esk10_1(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_8]),c_0_33]),c_0_9]),c_0_10]),c_0_11]),c_0_40]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_waybel_9(esk1_0,esk8_1(esk1_0))
    | ~ v5_pre_topc(k4_waybel_1(esk1_0,esk9_1(esk1_0)),esk1_0,esk1_0)
    | ~ m1_subset_1(esk10_1(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_42]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_37]),c_0_38]),c_0_39]),c_0_40])]),c_0_16]),c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk9_1(esk1_0),u1_struct_0(esk1_0))
    | ~ r1_waybel_9(esk1_0,esk8_1(esk1_0))
    | ~ m1_subset_1(esk10_1(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_42]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_37]),c_0_38]),c_0_39]),c_0_40])]),c_0_16]),c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk10_1(esk1_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk9_1(esk1_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_7]),c_0_8]),c_0_33]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_45])).

cnf(c_0_49,plain,
    ( v2_waybel_2(X1)
    | m1_subset_1(esk10_1(X1),u1_struct_0(X1))
    | m1_subset_1(esk9_1(X1),u1_struct_0(X1))
    | ~ r1_waybel_9(X1,esk8_1(X1))
    | ~ l1_waybel_9(X1)
    | ~ v1_compts_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_35]),c_0_29]),c_0_27]),c_0_25]),c_0_23]),c_0_31])).

cnf(c_0_50,plain,
    ( r1_waybel_9(X1,X2)
    | v2_struct_0(X2)
    | ~ v10_waybel_0(X2,X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v5_pre_topc(k4_waybel_1(X1,esk10_1(X1)),X1,X1)
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_compts_1(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_waybel_9(esk1_0,esk8_1(esk1_0))
    | ~ m1_subset_1(esk10_1(esk1_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_7]),c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk10_1(esk1_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_8]),c_0_33]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( r1_waybel_9(esk1_0,X1)
    | v2_struct_0(X1)
    | ~ v10_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ m1_subset_1(esk10_1(esk1_0),u1_struct_0(esk1_0))
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_7]),c_0_8]),c_0_33]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_waybel_9(esk1_0,esk8_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])])).

cnf(c_0_55,negated_conjecture,
    ( r1_waybel_9(esk1_0,X1)
    | v2_struct_0(X1)
    | ~ v10_waybel_0(X1,esk1_0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_52])])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_37]),c_0_38]),c_0_39]),c_0_40])]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
