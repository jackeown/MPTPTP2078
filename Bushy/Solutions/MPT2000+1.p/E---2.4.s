%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_7__t49_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:07 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 288 expanded)
%              Number of clauses        :   24 (  78 expanded)
%              Number of leaves         :    3 (  72 expanded)
%              Depth                    :    7
%              Number of atoms          :  299 (2997 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal clause size      :   76 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_waybel_7,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & v3_waybel_3(X1)
        & l1_orders_2(X1) )
     => ( v5_waybel_7(k1_waybel_4(X1),X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v4_waybel_7(X2,X1)
             => v5_waybel_6(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',t49_waybel_7)).

fof(l57_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & v3_waybel_3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ ( v5_waybel_7(k1_waybel_4(X1),X1)
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ~ ( r1_waybel_3(X1,k12_lattice3(X1,X3,X4),X2)
                          & ~ r3_orders_2(X1,X3,X2)
                          & ~ r3_orders_2(X1,X4,X2) ) ) )
              & ~ v5_waybel_6(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',l57_waybel_7)).

fof(t48_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & v3_waybel_3(X1)
        & l1_orders_2(X1) )
     => ( v5_waybel_7(k1_waybel_4(X1),X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v4_waybel_7(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ~ ( r1_waybel_3(X1,k12_lattice3(X1,X3,X4),X2)
                          & ~ r3_orders_2(X1,X3,X2)
                          & ~ r3_orders_2(X1,X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t49_waybel_7.p',t48_waybel_7)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_yellow_0(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & v3_waybel_3(X1)
          & l1_orders_2(X1) )
       => ( v5_waybel_7(k1_waybel_4(X1),X1)
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ( v4_waybel_7(X2,X1)
               => v5_waybel_6(X2,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_waybel_7])).

fof(c_0_4,plain,(
    ! [X24,X25] :
      ( ( m1_subset_1(esk6_2(X24,X25),u1_struct_0(X24))
        | ~ v5_waybel_7(k1_waybel_4(X24),X24)
        | v5_waybel_6(X25,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_yellow_0(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ v3_waybel_3(X24)
        | ~ l1_orders_2(X24) )
      & ( m1_subset_1(esk7_2(X24,X25),u1_struct_0(X24))
        | ~ v5_waybel_7(k1_waybel_4(X24),X24)
        | v5_waybel_6(X25,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_yellow_0(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ v3_waybel_3(X24)
        | ~ l1_orders_2(X24) )
      & ( r1_waybel_3(X24,k12_lattice3(X24,esk6_2(X24,X25),esk7_2(X24,X25)),X25)
        | ~ v5_waybel_7(k1_waybel_4(X24),X24)
        | v5_waybel_6(X25,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_yellow_0(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ v3_waybel_3(X24)
        | ~ l1_orders_2(X24) )
      & ( ~ r3_orders_2(X24,esk6_2(X24,X25),X25)
        | ~ v5_waybel_7(k1_waybel_4(X24),X24)
        | v5_waybel_6(X25,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_yellow_0(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ v3_waybel_3(X24)
        | ~ l1_orders_2(X24) )
      & ( ~ r3_orders_2(X24,esk7_2(X24,X25),X25)
        | ~ v5_waybel_7(k1_waybel_4(X24),X24)
        | v5_waybel_6(X25,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ v1_yellow_0(X24)
        | ~ v1_lattice3(X24)
        | ~ v2_lattice3(X24)
        | ~ v3_waybel_3(X24)
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l57_waybel_7])])])])])])).

fof(c_0_5,negated_conjecture,
    ( v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & v1_yellow_0(esk1_0)
    & v1_lattice3(esk1_0)
    & v2_lattice3(esk1_0)
    & v3_waybel_3(esk1_0)
    & l1_orders_2(esk1_0)
    & v5_waybel_7(k1_waybel_4(esk1_0),esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & v4_waybel_7(esk2_0,esk1_0)
    & ~ v5_waybel_6(esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X43,X44,X45,X46] :
      ( ( ~ v4_waybel_7(X44,X43)
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X46,u1_struct_0(X43))
        | ~ r1_waybel_3(X43,k12_lattice3(X43,X45,X46),X44)
        | r3_orders_2(X43,X45,X44)
        | r3_orders_2(X43,X46,X44)
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ v5_waybel_7(k1_waybel_4(X43),X43)
        | ~ v3_orders_2(X43)
        | ~ v4_orders_2(X43)
        | ~ v5_orders_2(X43)
        | ~ v1_yellow_0(X43)
        | ~ v1_lattice3(X43)
        | ~ v2_lattice3(X43)
        | ~ v3_waybel_3(X43)
        | ~ l1_orders_2(X43) )
      & ( m1_subset_1(esk8_2(X43,X44),u1_struct_0(X43))
        | v4_waybel_7(X44,X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ v5_waybel_7(k1_waybel_4(X43),X43)
        | ~ v3_orders_2(X43)
        | ~ v4_orders_2(X43)
        | ~ v5_orders_2(X43)
        | ~ v1_yellow_0(X43)
        | ~ v1_lattice3(X43)
        | ~ v2_lattice3(X43)
        | ~ v3_waybel_3(X43)
        | ~ l1_orders_2(X43) )
      & ( m1_subset_1(esk9_2(X43,X44),u1_struct_0(X43))
        | v4_waybel_7(X44,X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ v5_waybel_7(k1_waybel_4(X43),X43)
        | ~ v3_orders_2(X43)
        | ~ v4_orders_2(X43)
        | ~ v5_orders_2(X43)
        | ~ v1_yellow_0(X43)
        | ~ v1_lattice3(X43)
        | ~ v2_lattice3(X43)
        | ~ v3_waybel_3(X43)
        | ~ l1_orders_2(X43) )
      & ( r1_waybel_3(X43,k12_lattice3(X43,esk8_2(X43,X44),esk9_2(X43,X44)),X44)
        | v4_waybel_7(X44,X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ v5_waybel_7(k1_waybel_4(X43),X43)
        | ~ v3_orders_2(X43)
        | ~ v4_orders_2(X43)
        | ~ v5_orders_2(X43)
        | ~ v1_yellow_0(X43)
        | ~ v1_lattice3(X43)
        | ~ v2_lattice3(X43)
        | ~ v3_waybel_3(X43)
        | ~ l1_orders_2(X43) )
      & ( ~ r3_orders_2(X43,esk8_2(X43,X44),X44)
        | v4_waybel_7(X44,X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ v5_waybel_7(k1_waybel_4(X43),X43)
        | ~ v3_orders_2(X43)
        | ~ v4_orders_2(X43)
        | ~ v5_orders_2(X43)
        | ~ v1_yellow_0(X43)
        | ~ v1_lattice3(X43)
        | ~ v2_lattice3(X43)
        | ~ v3_waybel_3(X43)
        | ~ l1_orders_2(X43) )
      & ( ~ r3_orders_2(X43,esk9_2(X43,X44),X44)
        | v4_waybel_7(X44,X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ v5_waybel_7(k1_waybel_4(X43),X43)
        | ~ v3_orders_2(X43)
        | ~ v4_orders_2(X43)
        | ~ v5_orders_2(X43)
        | ~ v1_yellow_0(X43)
        | ~ v1_lattice3(X43)
        | ~ v2_lattice3(X43)
        | ~ v3_waybel_3(X43)
        | ~ l1_orders_2(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_waybel_7])])])])])])).

cnf(c_0_7,plain,
    ( r1_waybel_3(X1,k12_lattice3(X1,esk6_2(X1,X2),esk7_2(X1,X2)),X2)
    | v5_waybel_6(X2,X1)
    | ~ v5_waybel_7(k1_waybel_4(X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v5_waybel_7(k1_waybel_4(esk1_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( v3_waybel_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( v1_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( v1_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( ~ v5_waybel_6(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk7_2(X1,X2),u1_struct_0(X1))
    | v5_waybel_6(X2,X1)
    | ~ v5_waybel_7(k1_waybel_4(X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk6_2(X1,X2),u1_struct_0(X1))
    | v5_waybel_6(X2,X1)
    | ~ v5_waybel_7(k1_waybel_4(X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_21,plain,
    ( r3_orders_2(X2,X3,X1)
    | r3_orders_2(X2,X4,X1)
    | ~ v4_waybel_7(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_waybel_3(X2,k12_lattice3(X2,X3,X4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_waybel_7(k1_waybel_4(X2),X2)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v1_yellow_0(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ v3_waybel_3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( r1_waybel_3(esk1_0,k12_lattice3(esk1_0,esk6_2(esk1_0,esk2_0),esk7_2(esk1_0,esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v4_waybel_7(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk7_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk6_2(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_26,plain,
    ( v5_waybel_6(X2,X1)
    | ~ r3_orders_2(X1,esk7_2(X1,X2),X2)
    | ~ v5_waybel_7(k1_waybel_4(X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_27,negated_conjecture,
    ( r3_orders_2(esk1_0,esk7_2(esk1_0,esk2_0),esk2_0)
    | r3_orders_2(esk1_0,esk6_2(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_28,plain,
    ( v5_waybel_6(X2,X1)
    | ~ r3_orders_2(X1,esk6_2(X1,X2),X2)
    | ~ v5_waybel_7(k1_waybel_4(X1),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ v3_waybel_3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_29,negated_conjecture,
    ( r3_orders_2(esk1_0,esk6_2(esk1_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
