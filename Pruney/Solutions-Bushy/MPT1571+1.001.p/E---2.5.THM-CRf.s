%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1571+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:25 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 (5827 expanded)
%              Number of clauses        :   51 (2308 expanded)
%              Number of leaves         :    4 (1347 expanded)
%              Depth                    :   20
%              Number of atoms          :  233 (36349 expanded)
%              Number of equality atoms :   21 (3765 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( r2_yellow_0(X1,X2)
            & ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_lattice3(X1,X2,X4)
                <=> r1_lattice3(X1,X3,X4) ) ) )
         => k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_yellow_0)).

fof(t48_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_lattice3(X1,X2,X4)
                <=> r1_lattice3(X1,X3,X4) ) )
            & r2_yellow_0(X1,X2) )
         => r2_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_yellow_0)).

fof(d10_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_yellow_0(X1,X2)
           => ( X3 = k2_yellow_0(X1,X2)
            <=> ( r1_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

fof(dt_k2_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2,X3] :
            ( ( r2_yellow_0(X1,X2)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattice3(X1,X2,X4)
                  <=> r1_lattice3(X1,X3,X4) ) ) )
           => k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t49_yellow_0])).

fof(c_0_5,negated_conjecture,(
    ! [X19] :
      ( ~ v2_struct_0(esk3_0)
      & l1_orders_2(esk3_0)
      & r2_yellow_0(esk3_0,esk4_0)
      & ( ~ r1_lattice3(esk3_0,esk4_0,X19)
        | r1_lattice3(esk3_0,esk5_0,X19)
        | ~ m1_subset_1(X19,u1_struct_0(esk3_0)) )
      & ( ~ r1_lattice3(esk3_0,esk5_0,X19)
        | r1_lattice3(esk3_0,esk4_0,X19)
        | ~ m1_subset_1(X19,u1_struct_0(esk3_0)) )
      & k2_yellow_0(esk3_0,esk4_0) != k2_yellow_0(esk3_0,esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])])).

fof(c_0_6,plain,(
    ! [X12,X13,X14] :
      ( ( m1_subset_1(esk2_3(X12,X13,X14),u1_struct_0(X12))
        | ~ r2_yellow_0(X12,X13)
        | r2_yellow_0(X12,X14)
        | v2_struct_0(X12)
        | ~ l1_orders_2(X12) )
      & ( ~ r1_lattice3(X12,X13,esk2_3(X12,X13,X14))
        | ~ r1_lattice3(X12,X14,esk2_3(X12,X13,X14))
        | ~ r2_yellow_0(X12,X13)
        | r2_yellow_0(X12,X14)
        | v2_struct_0(X12)
        | ~ l1_orders_2(X12) )
      & ( r1_lattice3(X12,X13,esk2_3(X12,X13,X14))
        | r1_lattice3(X12,X14,esk2_3(X12,X13,X14))
        | ~ r2_yellow_0(X12,X13)
        | r2_yellow_0(X12,X14)
        | v2_struct_0(X12)
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_yellow_0])])])])])])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8] :
      ( ( r1_lattice3(X5,X6,X7)
        | X7 != k2_yellow_0(X5,X6)
        | ~ r2_yellow_0(X5,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( ~ m1_subset_1(X8,u1_struct_0(X5))
        | ~ r1_lattice3(X5,X6,X8)
        | r1_orders_2(X5,X8,X7)
        | X7 != k2_yellow_0(X5,X6)
        | ~ r2_yellow_0(X5,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))
        | ~ r1_lattice3(X5,X6,X7)
        | X7 = k2_yellow_0(X5,X6)
        | ~ r2_yellow_0(X5,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( r1_lattice3(X5,X6,esk1_3(X5,X6,X7))
        | ~ r1_lattice3(X5,X6,X7)
        | X7 = k2_yellow_0(X5,X6)
        | ~ r2_yellow_0(X5,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( ~ r1_orders_2(X5,esk1_3(X5,X6,X7),X7)
        | ~ r1_lattice3(X5,X6,X7)
        | X7 = k2_yellow_0(X5,X6)
        | ~ r2_yellow_0(X5,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_yellow_0])])])])])).

fof(c_0_8,plain,(
    ! [X10,X11] :
      ( ~ l1_orders_2(X10)
      | m1_subset_1(k2_yellow_0(X10,X11),u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).

cnf(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r1_lattice3(X1,X2,X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r1_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | r1_lattice3(X1,X3,esk2_3(X1,X2,X3))
    | r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | m1_subset_1(esk2_3(esk3_0,X2,X1),u1_struct_0(esk3_0))
    | ~ r2_yellow_0(esk3_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( r1_lattice3(X1,X2,k2_yellow_0(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,esk2_3(esk3_0,X1,X2))
    | r1_lattice3(esk3_0,X2,esk2_3(esk3_0,X1,X2))
    | r2_yellow_0(esk3_0,X2)
    | ~ r2_yellow_0(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_14]),c_0_11])])).

cnf(c_0_19,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,X1)
    | ~ r1_lattice3(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,negated_conjecture,
    ( r2_yellow_0(esk3_0,X1)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,X1),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,X1))
    | ~ r2_yellow_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,X1))
    | r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk4_0,X1))
    | r2_yellow_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,X1)
    | ~ r1_lattice3(esk3_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,X1))
    | r2_yellow_0(esk3_0,X1)
    | ~ r1_lattice3(esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,X1))
    | r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk4_0,X1))
    | r1_lattice3(esk3_0,X1,k2_yellow_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,X1))
    | r2_yellow_0(esk3_0,X1)
    | ~ r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,esk5_0))
    | r1_lattice3(esk3_0,esk5_0,k2_yellow_0(esk3_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_21])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k2_yellow_0(esk3_0,X1),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_11])).

cnf(c_0_30,plain,
    ( r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X3,esk2_3(X1,X2,X3))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0))
    | r1_lattice3(esk3_0,esk5_0,k2_yellow_0(esk3_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( k2_yellow_0(esk3_0,X1) = k2_yellow_0(esk3_0,X2)
    | m1_subset_1(esk1_3(esk3_0,X2,k2_yellow_0(esk3_0,X1)),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,X2,k2_yellow_0(esk3_0,X1))
    | ~ r2_yellow_0(esk3_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_11])])).

cnf(c_0_33,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,k2_yellow_0(esk3_0,X1))
    | ~ r1_lattice3(esk3_0,esk5_0,k2_yellow_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,k2_yellow_0(esk3_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_16]),c_0_11])]),c_0_9]),c_0_27]),c_0_21])).

cnf(c_0_35,plain,
    ( r1_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | X3 = k2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_37,negated_conjecture,
    ( k2_yellow_0(esk3_0,X1) = k2_yellow_0(esk3_0,esk4_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,k2_yellow_0(esk3_0,X1)),u1_struct_0(esk3_0))
    | ~ r1_lattice3(esk3_0,esk4_0,k2_yellow_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,k2_yellow_0(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k2_yellow_0(esk3_0,esk4_0) != k2_yellow_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_40,negated_conjecture,
    ( k2_yellow_0(esk3_0,X1) = k2_yellow_0(esk3_0,X2)
    | r1_lattice3(esk3_0,X2,esk1_3(esk3_0,X2,k2_yellow_0(esk3_0,X1)))
    | ~ r1_lattice3(esk3_0,X2,k2_yellow_0(esk3_0,X1))
    | ~ r2_yellow_0(esk3_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_29]),c_0_11])])).

cnf(c_0_41,plain,
    ( X3 = k2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_42,plain,
    ( r1_orders_2(X1,X2,k2_yellow_0(X1,X3))
    | ~ r1_lattice3(X1,X3,X2)
    | ~ r2_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_13])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,k2_yellow_0(esk3_0,esk5_0)),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( k2_yellow_0(esk3_0,X1) = k2_yellow_0(esk3_0,esk4_0)
    | r1_lattice3(esk3_0,esk4_0,esk1_3(esk3_0,esk4_0,k2_yellow_0(esk3_0,X1)))
    | ~ r1_lattice3(esk3_0,esk4_0,k2_yellow_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( k2_yellow_0(esk3_0,X1) = k2_yellow_0(esk3_0,X2)
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,X2,k2_yellow_0(esk3_0,X1)),k2_yellow_0(esk3_0,X1))
    | ~ r1_lattice3(esk3_0,X2,k2_yellow_0(esk3_0,X1))
    | ~ r2_yellow_0(esk3_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_29]),c_0_11])])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,k2_yellow_0(esk3_0,esk5_0)),k2_yellow_0(esk3_0,X1))
    | ~ r1_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,k2_yellow_0(esk3_0,esk5_0)))
    | ~ r2_yellow_0(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_11])])).

cnf(c_0_47,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk1_3(esk3_0,esk4_0,k2_yellow_0(esk3_0,esk5_0)))
    | ~ r1_lattice3(esk3_0,esk4_0,esk1_3(esk3_0,esk4_0,k2_yellow_0(esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,esk1_3(esk3_0,esk4_0,k2_yellow_0(esk3_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_38]),c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( k2_yellow_0(esk3_0,X1) = k2_yellow_0(esk3_0,esk4_0)
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,k2_yellow_0(esk3_0,X1)),k2_yellow_0(esk3_0,X1))
    | ~ r1_lattice3(esk3_0,esk4_0,k2_yellow_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_16])).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,k2_yellow_0(esk3_0,esk5_0)),k2_yellow_0(esk3_0,X1))
    | r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,X1))
    | r1_lattice3(esk3_0,X1,esk2_3(esk3_0,esk4_0,X1))
    | ~ r1_lattice3(esk3_0,X1,esk1_3(esk3_0,esk4_0,k2_yellow_0(esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk1_3(esk3_0,esk4_0,k2_yellow_0(esk3_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,k2_yellow_0(esk3_0,esk5_0)),k2_yellow_0(esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_38]),c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0))
    | r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,esk5_0))
    | r2_yellow_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( r1_lattice3(esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_54]),c_0_51])]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0))
    | r2_yellow_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_55])).

cnf(c_0_57,negated_conjecture,
    ( r1_lattice3(esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_56]),c_0_51])]),c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r2_yellow_0(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_57]),c_0_55]),c_0_16]),c_0_11])]),c_0_9])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_58]),c_0_51])]),c_0_52]),
    [proof]).

%------------------------------------------------------------------------------
