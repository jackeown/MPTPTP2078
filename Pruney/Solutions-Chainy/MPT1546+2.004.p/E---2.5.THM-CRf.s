%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:16 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 620 expanded)
%              Number of clauses        :   34 ( 212 expanded)
%              Number of leaves         :    5 ( 147 expanded)
%              Depth                    :   11
%              Number of atoms          :  271 (4326 expanded)
%              Number of equality atoms :   35 ( 601 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   74 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_yellow_0,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( X2 = k13_lattice3(X1,X2,X3)
              <=> r1_orders_2(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_0)).

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(l26_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k10_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X2,X4)
                      & r1_orders_2(X1,X3,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X2,X5)
                              & r1_orders_2(X1,X3,X5) )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( X2 = k13_lattice3(X1,X2,X3)
                <=> r1_orders_2(X1,X3,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_0])).

fof(c_0_6,plain,(
    ! [X15,X16,X17] :
      ( ~ v5_orders_2(X15)
      | ~ v1_lattice3(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | k13_lattice3(X15,X16,X17) = k10_lattice3(X15,X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

fof(c_0_7,negated_conjecture,
    ( v3_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & v1_lattice3(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & ( esk3_0 != k13_lattice3(esk2_0,esk3_0,esk4_0)
      | ~ r1_orders_2(esk2_0,esk4_0,esk3_0) )
    & ( esk3_0 = k13_lattice3(esk2_0,esk3_0,esk4_0)
      | r1_orders_2(esk2_0,esk4_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( r1_orders_2(X9,X10,X12)
        | X12 != k10_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ v5_orders_2(X9)
        | ~ v1_lattice3(X9)
        | ~ l1_orders_2(X9) )
      & ( r1_orders_2(X9,X11,X12)
        | X12 != k10_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ v5_orders_2(X9)
        | ~ v1_lattice3(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ m1_subset_1(X13,u1_struct_0(X9))
        | ~ r1_orders_2(X9,X10,X13)
        | ~ r1_orders_2(X9,X11,X13)
        | r1_orders_2(X9,X12,X13)
        | X12 != k10_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ v5_orders_2(X9)
        | ~ v1_lattice3(X9)
        | ~ l1_orders_2(X9) )
      & ( m1_subset_1(esk1_4(X9,X10,X11,X12),u1_struct_0(X9))
        | ~ r1_orders_2(X9,X10,X12)
        | ~ r1_orders_2(X9,X11,X12)
        | X12 = k10_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ v5_orders_2(X9)
        | ~ v1_lattice3(X9)
        | ~ l1_orders_2(X9) )
      & ( r1_orders_2(X9,X10,esk1_4(X9,X10,X11,X12))
        | ~ r1_orders_2(X9,X10,X12)
        | ~ r1_orders_2(X9,X11,X12)
        | X12 = k10_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ v5_orders_2(X9)
        | ~ v1_lattice3(X9)
        | ~ l1_orders_2(X9) )
      & ( r1_orders_2(X9,X11,esk1_4(X9,X10,X11,X12))
        | ~ r1_orders_2(X9,X10,X12)
        | ~ r1_orders_2(X9,X11,X12)
        | X12 = k10_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ v5_orders_2(X9)
        | ~ v1_lattice3(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ r1_orders_2(X9,X12,esk1_4(X9,X10,X11,X12))
        | ~ r1_orders_2(X9,X10,X12)
        | ~ r1_orders_2(X9,X11,X12)
        | X12 = k10_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ v5_orders_2(X9)
        | ~ v1_lattice3(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).

fof(c_0_9,plain,(
    ! [X8] :
      ( ~ l1_orders_2(X8)
      | ~ v1_lattice3(X8)
      | ~ v2_struct_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

cnf(c_0_10,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v1_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( r1_orders_2(X1,X2,esk1_4(X1,X2,X3,X4))
    | X4 = k10_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( X2 = k10_lattice3(X1,X3,X4)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,esk1_4(X1,X3,X4,X2))
    | ~ r1_orders_2(X1,X3,X2)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( k13_lattice3(esk2_0,X1,esk4_0) = k10_lattice3(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_20,plain,(
    ! [X6,X7] :
      ( v2_struct_0(X6)
      | ~ v3_orders_2(X6)
      | ~ l1_orders_2(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | r1_orders_2(X6,X7,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

cnf(c_0_21,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_orders_2(X2,X3,esk1_4(X2,X3,X4,X1))
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ r1_orders_2(X2,X1,esk1_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( esk3_0 = k13_lattice3(esk2_0,esk3_0,esk4_0)
    | r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) = k10_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( k10_lattice3(esk2_0,X1,X2) = esk3_0
    | r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X1,X2,esk3_0))
    | ~ r1_orders_2(esk2_0,X2,esk3_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_19]),c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k10_lattice3(esk2_0,X2,esk4_0)
    | ~ r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X2,esk4_0,X1))
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ r1_orders_2(esk2_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_11]),c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_29,negated_conjecture,
    ( k10_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk3_0)
    | v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_19]),c_0_14]),c_0_26])])).

cnf(c_0_31,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X3 != k10_lattice3(X1,X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( k10_lattice3(esk2_0,X1,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X1,esk4_0,esk3_0))
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( k10_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | k10_lattice3(esk2_0,X1,esk4_0) = esk3_0
    | ~ r1_orders_2(esk2_0,esk3_0,esk1_4(esk2_0,X1,esk4_0,esk3_0))
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_19])])).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_30]),c_0_13]),c_0_14])])).

cnf(c_0_35,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(k10_lattice3(X1,X3,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_31,c_0_16])])).

cnf(c_0_36,negated_conjecture,
    ( esk3_0 != k13_lattice3(esk2_0,esk3_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_37,negated_conjecture,
    ( k10_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | k10_lattice3(esk2_0,X1,esk4_0) = esk3_0
    | r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X1,esk4_0,esk3_0))
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( k10_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0
    | ~ r1_orders_2(esk2_0,esk3_0,esk1_4(esk2_0,esk3_0,esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_19])])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,k10_lattice3(esk2_0,esk3_0,X1))
    | ~ m1_subset_1(k10_lattice3(esk2_0,esk3_0,X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_19]),c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_40,negated_conjecture,
    ( k10_lattice3(esk2_0,esk3_0,esk4_0) != esk3_0
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_24])).

cnf(c_0_41,negated_conjecture,
    ( k10_lattice3(esk2_0,esk3_0,esk4_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_19]),c_0_34])]),c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,k10_lattice3(esk2_0,esk3_0,esk4_0))
    | ~ m1_subset_1(k10_lattice3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_11])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_41]),c_0_41]),c_0_19])]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:06:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.19/0.39  # and selection function SelectNewComplexAHP.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.038 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t24_yellow_0, conjecture, ![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X2=k13_lattice3(X1,X2,X3)<=>r1_orders_2(X1,X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow_0)).
% 0.19/0.39  fof(redefinition_k13_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 0.19/0.39  fof(l26_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k10_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 0.19/0.39  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.19/0.39  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 0.19/0.39  fof(c_0_5, negated_conjecture, ~(![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X2=k13_lattice3(X1,X2,X3)<=>r1_orders_2(X1,X3,X2)))))), inference(assume_negation,[status(cth)],[t24_yellow_0])).
% 0.19/0.39  fof(c_0_6, plain, ![X15, X16, X17]:(~v5_orders_2(X15)|~v1_lattice3(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|k13_lattice3(X15,X16,X17)=k10_lattice3(X15,X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).
% 0.19/0.39  fof(c_0_7, negated_conjecture, ((((v3_orders_2(esk2_0)&v5_orders_2(esk2_0))&v1_lattice3(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&((esk3_0!=k13_lattice3(esk2_0,esk3_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0))&(esk3_0=k13_lattice3(esk2_0,esk3_0,esk4_0)|r1_orders_2(esk2_0,esk4_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.19/0.39  fof(c_0_8, plain, ![X9, X10, X11, X12, X13]:((((r1_orders_2(X9,X10,X12)|X12!=k10_lattice3(X9,X10,X11)|~m1_subset_1(X12,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~v5_orders_2(X9)|~v1_lattice3(X9)|~l1_orders_2(X9)))&(r1_orders_2(X9,X11,X12)|X12!=k10_lattice3(X9,X10,X11)|~m1_subset_1(X12,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~v5_orders_2(X9)|~v1_lattice3(X9)|~l1_orders_2(X9))))&(~m1_subset_1(X13,u1_struct_0(X9))|(~r1_orders_2(X9,X10,X13)|~r1_orders_2(X9,X11,X13)|r1_orders_2(X9,X12,X13))|X12!=k10_lattice3(X9,X10,X11)|~m1_subset_1(X12,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~v5_orders_2(X9)|~v1_lattice3(X9)|~l1_orders_2(X9))))&((m1_subset_1(esk1_4(X9,X10,X11,X12),u1_struct_0(X9))|(~r1_orders_2(X9,X10,X12)|~r1_orders_2(X9,X11,X12))|X12=k10_lattice3(X9,X10,X11)|~m1_subset_1(X12,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~v5_orders_2(X9)|~v1_lattice3(X9)|~l1_orders_2(X9)))&(((r1_orders_2(X9,X10,esk1_4(X9,X10,X11,X12))|(~r1_orders_2(X9,X10,X12)|~r1_orders_2(X9,X11,X12))|X12=k10_lattice3(X9,X10,X11)|~m1_subset_1(X12,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~v5_orders_2(X9)|~v1_lattice3(X9)|~l1_orders_2(X9)))&(r1_orders_2(X9,X11,esk1_4(X9,X10,X11,X12))|(~r1_orders_2(X9,X10,X12)|~r1_orders_2(X9,X11,X12))|X12=k10_lattice3(X9,X10,X11)|~m1_subset_1(X12,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~v5_orders_2(X9)|~v1_lattice3(X9)|~l1_orders_2(X9))))&(~r1_orders_2(X9,X12,esk1_4(X9,X10,X11,X12))|(~r1_orders_2(X9,X10,X12)|~r1_orders_2(X9,X11,X12))|X12=k10_lattice3(X9,X10,X11)|~m1_subset_1(X12,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~v5_orders_2(X9)|~v1_lattice3(X9)|~l1_orders_2(X9)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).
% 0.19/0.39  fof(c_0_9, plain, ![X8]:(~l1_orders_2(X8)|(~v1_lattice3(X8)|~v2_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.19/0.39  cnf(c_0_10, plain, (k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  cnf(c_0_12, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  cnf(c_0_13, negated_conjecture, (v1_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  cnf(c_0_14, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  cnf(c_0_15, plain, (r1_orders_2(X1,X2,esk1_4(X1,X2,X3,X4))|X4=k10_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_16, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_17, plain, (X2=k10_lattice3(X1,X3,X4)|v2_struct_0(X1)|~r1_orders_2(X1,X2,esk1_4(X1,X3,X4,X2))|~r1_orders_2(X1,X3,X2)|~r1_orders_2(X1,X4,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_18, negated_conjecture, (k13_lattice3(esk2_0,X1,esk4_0)=k10_lattice3(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13]), c_0_14])])).
% 0.19/0.39  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  fof(c_0_20, plain, ![X6, X7]:(v2_struct_0(X6)|~v3_orders_2(X6)|~l1_orders_2(X6)|(~m1_subset_1(X7,u1_struct_0(X6))|r1_orders_2(X6,X7,X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.19/0.39  cnf(c_0_21, plain, (X1=k10_lattice3(X2,X3,X4)|r1_orders_2(X2,X3,esk1_4(X2,X3,X4,X1))|~v5_orders_2(X2)|~v1_lattice3(X2)|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.39  cnf(c_0_22, plain, (X1=k10_lattice3(X2,X3,X4)|~v5_orders_2(X2)|~v1_lattice3(X2)|~r1_orders_2(X2,X1,esk1_4(X2,X3,X4,X1))|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_17, c_0_16])).
% 0.19/0.39  cnf(c_0_23, negated_conjecture, (esk3_0=k13_lattice3(esk2_0,esk3_0,esk4_0)|r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  cnf(c_0_24, negated_conjecture, (k13_lattice3(esk2_0,esk3_0,esk4_0)=k10_lattice3(esk2_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.39  cnf(c_0_25, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  cnf(c_0_26, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  cnf(c_0_27, negated_conjecture, (k10_lattice3(esk2_0,X1,X2)=esk3_0|r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X1,X2,esk3_0))|~r1_orders_2(esk2_0,X2,esk3_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_19]), c_0_12]), c_0_13]), c_0_14])])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (X1=k10_lattice3(esk2_0,X2,esk4_0)|~r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X2,esk4_0,X1))|~r1_orders_2(esk2_0,esk4_0,X1)|~r1_orders_2(esk2_0,X2,X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_11]), c_0_12]), c_0_13]), c_0_14])])).
% 0.19/0.39  cnf(c_0_29, negated_conjecture, (k10_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk3_0)|v2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_19]), c_0_14]), c_0_26])])).
% 0.19/0.39  cnf(c_0_31, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X3!=k10_lattice3(X1,X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_32, negated_conjecture, (k10_lattice3(esk2_0,X1,esk4_0)=esk3_0|r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X1,esk4_0,esk3_0))|~r1_orders_2(esk2_0,esk4_0,esk3_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_27, c_0_11])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (k10_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|k10_lattice3(esk2_0,X1,esk4_0)=esk3_0|~r1_orders_2(esk2_0,esk3_0,esk1_4(esk2_0,X1,esk4_0,esk3_0))|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_19])])).
% 0.19/0.39  cnf(c_0_34, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_30]), c_0_13]), c_0_14])])).
% 0.19/0.39  cnf(c_0_35, plain, (r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))|~v5_orders_2(X1)|~v1_lattice3(X1)|~m1_subset_1(k10_lattice3(X1,X3,X2),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_31, c_0_16])])).
% 0.19/0.39  cnf(c_0_36, negated_conjecture, (esk3_0!=k13_lattice3(esk2_0,esk3_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.39  cnf(c_0_37, negated_conjecture, (k10_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|k10_lattice3(esk2_0,X1,esk4_0)=esk3_0|r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X1,esk4_0,esk3_0))|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_29])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (k10_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0|~r1_orders_2(esk2_0,esk3_0,esk1_4(esk2_0,esk3_0,esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_19])])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (r1_orders_2(esk2_0,X1,k10_lattice3(esk2_0,esk3_0,X1))|~m1_subset_1(k10_lattice3(esk2_0,esk3_0,X1),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_19]), c_0_12]), c_0_13]), c_0_14])])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (k10_lattice3(esk2_0,esk3_0,esk4_0)!=esk3_0|~r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(rw,[status(thm)],[c_0_36, c_0_24])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (k10_lattice3(esk2_0,esk3_0,esk4_0)=esk3_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_19]), c_0_34])]), c_0_38])).
% 0.19/0.39  cnf(c_0_42, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,k10_lattice3(esk2_0,esk3_0,esk4_0))|~m1_subset_1(k10_lattice3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_39, c_0_11])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (~r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])])).
% 0.19/0.39  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_41]), c_0_41]), c_0_19])]), c_0_43]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 45
% 0.19/0.39  # Proof object clause steps            : 34
% 0.19/0.39  # Proof object formula steps           : 11
% 0.19/0.39  # Proof object conjectures             : 28
% 0.19/0.39  # Proof object clause conjectures      : 25
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 14
% 0.19/0.39  # Proof object initial formulas used   : 5
% 0.19/0.39  # Proof object generating inferences   : 13
% 0.19/0.39  # Proof object simplifying inferences  : 42
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 5
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 18
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 18
% 0.19/0.39  # Processed clauses                    : 153
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 3
% 0.19/0.39  # ...remaining for further processing  : 149
% 0.19/0.39  # Other redundant clauses eliminated   : 3
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 12
% 0.19/0.39  # Backward-rewritten                   : 58
% 0.19/0.39  # Generated clauses                    : 237
% 0.19/0.39  # ...of the previous two non-trivial   : 242
% 0.19/0.39  # Contextual simplify-reflections      : 14
% 0.19/0.39  # Paramodulations                      : 234
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 3
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 58
% 0.19/0.39  #    Positive orientable unit clauses  : 14
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 1
% 0.19/0.39  #    Non-unit-clauses                  : 43
% 0.19/0.39  # Current number of unprocessed clauses: 66
% 0.19/0.39  # ...number of literals in the above   : 340
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 88
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 1366
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 264
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 29
% 0.19/0.39  # Unit Clause-clause subsumption calls : 46
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 20
% 0.19/0.39  # BW rewrite match successes           : 6
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 11185
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.050 s
% 0.19/0.39  # System time              : 0.007 s
% 0.19/0.39  # Total time               : 0.057 s
% 0.19/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
