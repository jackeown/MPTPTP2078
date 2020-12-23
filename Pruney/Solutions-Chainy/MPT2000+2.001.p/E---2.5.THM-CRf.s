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
% DateTime   : Thu Dec  3 11:21:32 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 291 expanded)
%              Number of clauses        :   27 (  81 expanded)
%              Number of leaves         :    3 (  72 expanded)
%              Depth                    :    8
%              Number of atoms          :  308 (3006 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   6 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_waybel_7)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_waybel_7)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_waybel_7)).

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
    ! [X5,X6] :
      ( ( m1_subset_1(esk1_2(X5,X6),u1_struct_0(X5))
        | ~ v5_waybel_7(k1_waybel_4(X5),X5)
        | v5_waybel_6(X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v1_yellow_0(X5)
        | ~ v1_lattice3(X5)
        | ~ v2_lattice3(X5)
        | ~ v3_waybel_3(X5)
        | ~ l1_orders_2(X5) )
      & ( m1_subset_1(esk2_2(X5,X6),u1_struct_0(X5))
        | ~ v5_waybel_7(k1_waybel_4(X5),X5)
        | v5_waybel_6(X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v1_yellow_0(X5)
        | ~ v1_lattice3(X5)
        | ~ v2_lattice3(X5)
        | ~ v3_waybel_3(X5)
        | ~ l1_orders_2(X5) )
      & ( r1_waybel_3(X5,k12_lattice3(X5,esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | ~ v5_waybel_7(k1_waybel_4(X5),X5)
        | v5_waybel_6(X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v1_yellow_0(X5)
        | ~ v1_lattice3(X5)
        | ~ v2_lattice3(X5)
        | ~ v3_waybel_3(X5)
        | ~ l1_orders_2(X5) )
      & ( ~ r3_orders_2(X5,esk1_2(X5,X6),X6)
        | ~ v5_waybel_7(k1_waybel_4(X5),X5)
        | v5_waybel_6(X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v1_yellow_0(X5)
        | ~ v1_lattice3(X5)
        | ~ v2_lattice3(X5)
        | ~ v3_waybel_3(X5)
        | ~ l1_orders_2(X5) )
      & ( ~ r3_orders_2(X5,esk2_2(X5,X6),X6)
        | ~ v5_waybel_7(k1_waybel_4(X5),X5)
        | v5_waybel_6(X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v3_orders_2(X5)
        | ~ v4_orders_2(X5)
        | ~ v5_orders_2(X5)
        | ~ v1_yellow_0(X5)
        | ~ v1_lattice3(X5)
        | ~ v2_lattice3(X5)
        | ~ v3_waybel_3(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l57_waybel_7])])])])])])).

fof(c_0_5,negated_conjecture,
    ( v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & v1_yellow_0(esk5_0)
    & v1_lattice3(esk5_0)
    & v2_lattice3(esk5_0)
    & v3_waybel_3(esk5_0)
    & l1_orders_2(esk5_0)
    & v5_waybel_7(k1_waybel_4(esk5_0),esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & v4_waybel_7(esk6_0,esk5_0)
    & ~ v5_waybel_6(esk6_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( r1_waybel_3(X1,k12_lattice3(X1,esk1_2(X1,X2),esk2_2(X1,X2)),X2)
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

cnf(c_0_7,negated_conjecture,
    ( v5_waybel_7(k1_waybel_4(esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v3_waybel_3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v2_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( v1_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( v1_yellow_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
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

cnf(c_0_17,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
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

fof(c_0_18,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ v4_waybel_7(X10,X9)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ r1_waybel_3(X9,k12_lattice3(X9,X11,X12),X10)
        | r3_orders_2(X9,X11,X10)
        | r3_orders_2(X9,X12,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ v5_waybel_7(k1_waybel_4(X9),X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ v1_yellow_0(X9)
        | ~ v1_lattice3(X9)
        | ~ v2_lattice3(X9)
        | ~ v3_waybel_3(X9)
        | ~ l1_orders_2(X9) )
      & ( m1_subset_1(esk3_2(X9,X10),u1_struct_0(X9))
        | v4_waybel_7(X10,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ v5_waybel_7(k1_waybel_4(X9),X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ v1_yellow_0(X9)
        | ~ v1_lattice3(X9)
        | ~ v2_lattice3(X9)
        | ~ v3_waybel_3(X9)
        | ~ l1_orders_2(X9) )
      & ( m1_subset_1(esk4_2(X9,X10),u1_struct_0(X9))
        | v4_waybel_7(X10,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ v5_waybel_7(k1_waybel_4(X9),X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ v1_yellow_0(X9)
        | ~ v1_lattice3(X9)
        | ~ v2_lattice3(X9)
        | ~ v3_waybel_3(X9)
        | ~ l1_orders_2(X9) )
      & ( r1_waybel_3(X9,k12_lattice3(X9,esk3_2(X9,X10),esk4_2(X9,X10)),X10)
        | v4_waybel_7(X10,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ v5_waybel_7(k1_waybel_4(X9),X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ v1_yellow_0(X9)
        | ~ v1_lattice3(X9)
        | ~ v2_lattice3(X9)
        | ~ v3_waybel_3(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ r3_orders_2(X9,esk3_2(X9,X10),X10)
        | v4_waybel_7(X10,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ v5_waybel_7(k1_waybel_4(X9),X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ v1_yellow_0(X9)
        | ~ v1_lattice3(X9)
        | ~ v2_lattice3(X9)
        | ~ v3_waybel_3(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ r3_orders_2(X9,esk4_2(X9,X10),X10)
        | v4_waybel_7(X10,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ v5_waybel_7(k1_waybel_4(X9),X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ v1_yellow_0(X9)
        | ~ v1_lattice3(X9)
        | ~ v2_lattice3(X9)
        | ~ v3_waybel_3(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_waybel_7])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( v5_waybel_6(X1,esk5_0)
    | r1_waybel_3(esk5_0,k12_lattice3(esk5_0,esk1_2(esk5_0,X1),esk2_2(esk5_0,X1)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( ~ v5_waybel_6(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( v5_waybel_6(X1,esk5_0)
    | m1_subset_1(esk2_2(esk5_0,X1),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_23,negated_conjecture,
    ( v5_waybel_6(X1,esk5_0)
    | m1_subset_1(esk1_2(esk5_0,X1),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_24,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r1_waybel_3(esk5_0,k12_lattice3(esk5_0,esk1_2(esk5_0,esk6_0),esk2_2(esk5_0,esk6_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( v4_waybel_7(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk2_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_20]),c_0_21])).

cnf(c_0_29,plain,
    ( v5_waybel_6(X2,X1)
    | ~ r3_orders_2(X1,esk2_2(X1,X2),X2)
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

cnf(c_0_30,negated_conjecture,
    ( r3_orders_2(esk5_0,esk1_2(esk5_0,esk6_0),esk6_0)
    | r3_orders_2(esk5_0,esk2_2(esk5_0,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_7]),c_0_27]),c_0_28]),c_0_20]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_31,plain,
    ( v5_waybel_6(X2,X1)
    | ~ r3_orders_2(X1,esk1_2(X1,X2),X2)
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

cnf(c_0_32,negated_conjecture,
    ( r3_orders_2(esk5_0,esk1_2(esk5_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_7]),c_0_20]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_7]),c_0_20]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:17:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t49_waybel_7, conjecture, ![X1]:((((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v3_waybel_3(X1))&l1_orders_2(X1))=>(v5_waybel_7(k1_waybel_4(X1),X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v4_waybel_7(X2,X1)=>v5_waybel_6(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_waybel_7)).
% 0.12/0.37  fof(l57_waybel_7, axiom, ![X1]:((((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v3_waybel_3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~(((v5_waybel_7(k1_waybel_4(X1),X1)&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~(((r1_waybel_3(X1,k12_lattice3(X1,X3,X4),X2)&~(r3_orders_2(X1,X3,X2)))&~(r3_orders_2(X1,X4,X2)))))))&~(v5_waybel_6(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_waybel_7)).
% 0.12/0.37  fof(t48_waybel_7, axiom, ![X1]:((((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v3_waybel_3(X1))&l1_orders_2(X1))=>(v5_waybel_7(k1_waybel_4(X1),X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v4_waybel_7(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~(((r1_waybel_3(X1,k12_lattice3(X1,X3,X4),X2)&~(r3_orders_2(X1,X3,X2)))&~(r3_orders_2(X1,X4,X2)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_waybel_7)).
% 0.12/0.37  fof(c_0_3, negated_conjecture, ~(![X1]:((((((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&v1_lattice3(X1))&v2_lattice3(X1))&v3_waybel_3(X1))&l1_orders_2(X1))=>(v5_waybel_7(k1_waybel_4(X1),X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v4_waybel_7(X2,X1)=>v5_waybel_6(X2,X1)))))), inference(assume_negation,[status(cth)],[t49_waybel_7])).
% 0.12/0.37  fof(c_0_4, plain, ![X5, X6]:((m1_subset_1(esk1_2(X5,X6),u1_struct_0(X5))|~v5_waybel_7(k1_waybel_4(X5),X5)|v5_waybel_6(X6,X5)|~m1_subset_1(X6,u1_struct_0(X5))|(~v3_orders_2(X5)|~v4_orders_2(X5)|~v5_orders_2(X5)|~v1_yellow_0(X5)|~v1_lattice3(X5)|~v2_lattice3(X5)|~v3_waybel_3(X5)|~l1_orders_2(X5)))&((m1_subset_1(esk2_2(X5,X6),u1_struct_0(X5))|~v5_waybel_7(k1_waybel_4(X5),X5)|v5_waybel_6(X6,X5)|~m1_subset_1(X6,u1_struct_0(X5))|(~v3_orders_2(X5)|~v4_orders_2(X5)|~v5_orders_2(X5)|~v1_yellow_0(X5)|~v1_lattice3(X5)|~v2_lattice3(X5)|~v3_waybel_3(X5)|~l1_orders_2(X5)))&(((r1_waybel_3(X5,k12_lattice3(X5,esk1_2(X5,X6),esk2_2(X5,X6)),X6)|~v5_waybel_7(k1_waybel_4(X5),X5)|v5_waybel_6(X6,X5)|~m1_subset_1(X6,u1_struct_0(X5))|(~v3_orders_2(X5)|~v4_orders_2(X5)|~v5_orders_2(X5)|~v1_yellow_0(X5)|~v1_lattice3(X5)|~v2_lattice3(X5)|~v3_waybel_3(X5)|~l1_orders_2(X5)))&(~r3_orders_2(X5,esk1_2(X5,X6),X6)|~v5_waybel_7(k1_waybel_4(X5),X5)|v5_waybel_6(X6,X5)|~m1_subset_1(X6,u1_struct_0(X5))|(~v3_orders_2(X5)|~v4_orders_2(X5)|~v5_orders_2(X5)|~v1_yellow_0(X5)|~v1_lattice3(X5)|~v2_lattice3(X5)|~v3_waybel_3(X5)|~l1_orders_2(X5))))&(~r3_orders_2(X5,esk2_2(X5,X6),X6)|~v5_waybel_7(k1_waybel_4(X5),X5)|v5_waybel_6(X6,X5)|~m1_subset_1(X6,u1_struct_0(X5))|(~v3_orders_2(X5)|~v4_orders_2(X5)|~v5_orders_2(X5)|~v1_yellow_0(X5)|~v1_lattice3(X5)|~v2_lattice3(X5)|~v3_waybel_3(X5)|~l1_orders_2(X5)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l57_waybel_7])])])])])])).
% 0.12/0.37  fof(c_0_5, negated_conjecture, ((((((((v3_orders_2(esk5_0)&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&v1_yellow_0(esk5_0))&v1_lattice3(esk5_0))&v2_lattice3(esk5_0))&v3_waybel_3(esk5_0))&l1_orders_2(esk5_0))&(v5_waybel_7(k1_waybel_4(esk5_0),esk5_0)&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&(v4_waybel_7(esk6_0,esk5_0)&~v5_waybel_6(esk6_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.12/0.37  cnf(c_0_6, plain, (r1_waybel_3(X1,k12_lattice3(X1,esk1_2(X1,X2),esk2_2(X1,X2)),X2)|v5_waybel_6(X2,X1)|~v5_waybel_7(k1_waybel_4(X1),X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v3_waybel_3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_7, negated_conjecture, (v5_waybel_7(k1_waybel_4(esk5_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_8, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_9, negated_conjecture, (v3_waybel_3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_10, negated_conjecture, (v2_lattice3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_11, negated_conjecture, (v1_lattice3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_12, negated_conjecture, (v1_yellow_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_16, plain, (m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))|v5_waybel_6(X2,X1)|~v5_waybel_7(k1_waybel_4(X1),X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v3_waybel_3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_17, plain, (m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|v5_waybel_6(X2,X1)|~v5_waybel_7(k1_waybel_4(X1),X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v3_waybel_3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  fof(c_0_18, plain, ![X9, X10, X11, X12]:((~v4_waybel_7(X10,X9)|(~m1_subset_1(X11,u1_struct_0(X9))|(~m1_subset_1(X12,u1_struct_0(X9))|(~r1_waybel_3(X9,k12_lattice3(X9,X11,X12),X10)|r3_orders_2(X9,X11,X10)|r3_orders_2(X9,X12,X10))))|~m1_subset_1(X10,u1_struct_0(X9))|~v5_waybel_7(k1_waybel_4(X9),X9)|(~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~v1_yellow_0(X9)|~v1_lattice3(X9)|~v2_lattice3(X9)|~v3_waybel_3(X9)|~l1_orders_2(X9)))&((m1_subset_1(esk3_2(X9,X10),u1_struct_0(X9))|v4_waybel_7(X10,X9)|~m1_subset_1(X10,u1_struct_0(X9))|~v5_waybel_7(k1_waybel_4(X9),X9)|(~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~v1_yellow_0(X9)|~v1_lattice3(X9)|~v2_lattice3(X9)|~v3_waybel_3(X9)|~l1_orders_2(X9)))&((m1_subset_1(esk4_2(X9,X10),u1_struct_0(X9))|v4_waybel_7(X10,X9)|~m1_subset_1(X10,u1_struct_0(X9))|~v5_waybel_7(k1_waybel_4(X9),X9)|(~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~v1_yellow_0(X9)|~v1_lattice3(X9)|~v2_lattice3(X9)|~v3_waybel_3(X9)|~l1_orders_2(X9)))&(((r1_waybel_3(X9,k12_lattice3(X9,esk3_2(X9,X10),esk4_2(X9,X10)),X10)|v4_waybel_7(X10,X9)|~m1_subset_1(X10,u1_struct_0(X9))|~v5_waybel_7(k1_waybel_4(X9),X9)|(~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~v1_yellow_0(X9)|~v1_lattice3(X9)|~v2_lattice3(X9)|~v3_waybel_3(X9)|~l1_orders_2(X9)))&(~r3_orders_2(X9,esk3_2(X9,X10),X10)|v4_waybel_7(X10,X9)|~m1_subset_1(X10,u1_struct_0(X9))|~v5_waybel_7(k1_waybel_4(X9),X9)|(~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~v1_yellow_0(X9)|~v1_lattice3(X9)|~v2_lattice3(X9)|~v3_waybel_3(X9)|~l1_orders_2(X9))))&(~r3_orders_2(X9,esk4_2(X9,X10),X10)|v4_waybel_7(X10,X9)|~m1_subset_1(X10,u1_struct_0(X9))|~v5_waybel_7(k1_waybel_4(X9),X9)|(~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~v1_yellow_0(X9)|~v1_lattice3(X9)|~v2_lattice3(X9)|~v3_waybel_3(X9)|~l1_orders_2(X9))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_waybel_7])])])])])])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (v5_waybel_6(X1,esk5_0)|r1_waybel_3(esk5_0,k12_lattice3(esk5_0,esk1_2(esk5_0,X1),esk2_2(esk5_0,X1)),X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15])])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (~v5_waybel_6(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (v5_waybel_6(X1,esk5_0)|m1_subset_1(esk2_2(esk5_0,X1),u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_7]), c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15])])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (v5_waybel_6(X1,esk5_0)|m1_subset_1(esk1_2(esk5_0,X1),u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_7]), c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15])])).
% 0.12/0.37  cnf(c_0_24, plain, (r3_orders_2(X2,X3,X1)|r3_orders_2(X2,X4,X1)|~v4_waybel_7(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r1_waybel_3(X2,k12_lattice3(X2,X3,X4),X1)|~m1_subset_1(X1,u1_struct_0(X2))|~v5_waybel_7(k1_waybel_4(X2),X2)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~v1_yellow_0(X2)|~v1_lattice3(X2)|~v2_lattice3(X2)|~v3_waybel_3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (r1_waybel_3(esk5_0,k12_lattice3(esk5_0,esk1_2(esk5_0,esk6_0),esk2_2(esk5_0,esk6_0)),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (v4_waybel_7(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk2_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_20]), c_0_21])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk1_2(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_20]), c_0_21])).
% 0.12/0.37  cnf(c_0_29, plain, (v5_waybel_6(X2,X1)|~r3_orders_2(X1,esk2_2(X1,X2),X2)|~v5_waybel_7(k1_waybel_4(X1),X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v3_waybel_3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (r3_orders_2(esk5_0,esk1_2(esk5_0,esk6_0),esk6_0)|r3_orders_2(esk5_0,esk2_2(esk5_0,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_7]), c_0_27]), c_0_28]), c_0_20]), c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15])])).
% 0.12/0.37  cnf(c_0_31, plain, (v5_waybel_6(X2,X1)|~r3_orders_2(X1,esk1_2(X1,X2),X2)|~v5_waybel_7(k1_waybel_4(X1),X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~v3_waybel_3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (r3_orders_2(esk5_0,esk1_2(esk5_0,esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_7]), c_0_20]), c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_21])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_7]), c_0_20]), c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_21]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 34
% 0.12/0.37  # Proof object clause steps            : 27
% 0.12/0.37  # Proof object formula steps           : 7
% 0.12/0.37  # Proof object conjectures             : 24
% 0.12/0.37  # Proof object clause conjectures      : 21
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 18
% 0.12/0.37  # Proof object initial formulas used   : 3
% 0.12/0.37  # Proof object generating inferences   : 9
% 0.12/0.37  # Proof object simplifying inferences  : 68
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 3
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 23
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 23
% 0.12/0.37  # Processed clauses                    : 64
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 64
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 1
% 0.12/0.37  # Generated clauses                    : 64
% 0.12/0.37  # ...of the previous two non-trivial   : 61
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 64
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 40
% 0.12/0.37  #    Positive orientable unit clauses  : 15
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 24
% 0.12/0.37  # Current number of unprocessed clauses: 43
% 0.12/0.37  # ...number of literals in the above   : 127
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 24
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 192
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 51
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 12
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 2
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 4802
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.035 s
% 0.12/0.37  # System time              : 0.001 s
% 0.12/0.37  # Total time               : 0.036 s
% 0.12/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
