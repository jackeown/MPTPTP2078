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
% DateTime   : Thu Dec  3 11:14:54 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 245 expanded)
%              Number of clauses        :   34 (  89 expanded)
%              Number of leaves         :    4 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  339 (1984 expanded)
%              Number of equality atoms :   31 ( 208 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal clause size      :   74 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(dt_k10_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(t13_lattice3,conjecture,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k10_lattice3(X1,X2,X3) = k10_lattice3(X1,X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_lattice3)).

fof(c_0_4,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( r1_orders_2(X10,X11,X13)
        | X13 != k10_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v5_orders_2(X10)
        | ~ v1_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,X12,X13)
        | X13 != k10_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v5_orders_2(X10)
        | ~ v1_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ m1_subset_1(X14,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X11,X14)
        | ~ r1_orders_2(X10,X12,X14)
        | r1_orders_2(X10,X13,X14)
        | X13 != k10_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v5_orders_2(X10)
        | ~ v1_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk1_4(X10,X11,X12,X13),u1_struct_0(X10))
        | ~ r1_orders_2(X10,X11,X13)
        | ~ r1_orders_2(X10,X12,X13)
        | X13 = k10_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v5_orders_2(X10)
        | ~ v1_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,X11,esk1_4(X10,X11,X12,X13))
        | ~ r1_orders_2(X10,X11,X13)
        | ~ r1_orders_2(X10,X12,X13)
        | X13 = k10_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v5_orders_2(X10)
        | ~ v1_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,X12,esk1_4(X10,X11,X12,X13))
        | ~ r1_orders_2(X10,X11,X13)
        | ~ r1_orders_2(X10,X12,X13)
        | X13 = k10_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v5_orders_2(X10)
        | ~ v1_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,X13,esk1_4(X10,X11,X12,X13))
        | ~ r1_orders_2(X10,X11,X13)
        | ~ r1_orders_2(X10,X12,X13)
        | X13 = k10_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v5_orders_2(X10)
        | ~ v1_lattice3(X10)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).

fof(c_0_5,plain,(
    ! [X6] :
      ( ~ l1_orders_2(X6)
      | ~ v1_lattice3(X6)
      | ~ v2_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

cnf(c_0_6,plain,
    ( r1_orders_2(X2,X5,X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | X5 != k10_lattice3(X2,X3,X4)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X7,X8,X9] :
      ( ~ l1_orders_2(X7)
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | m1_subset_1(k10_lattice3(X7,X8,X9),u1_struct_0(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v5_orders_2(X1)
          & v1_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k10_lattice3(X1,X2,X3) = k10_lattice3(X1,X3,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t13_lattice3])).

cnf(c_0_10,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k10_lattice3(X1,X4,X5)
    | ~ r1_orders_2(X1,X5,X3)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_11,plain,
    ( m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,
    ( v5_orders_2(esk2_0)
    & v1_lattice3(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & k10_lattice3(esk2_0,esk3_0,esk4_0) != k10_lattice3(esk2_0,esk4_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_13,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X3 != k10_lattice3(X1,X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,plain,
    ( r1_orders_2(X1,k10_lattice3(X1,X2,X3),X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X4,X2)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_13,c_0_7])).

cnf(c_0_20,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_21,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | ~ r1_orders_2(X2,X1,esk1_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ v5_orders_2(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_14,c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( r1_orders_2(esk2_0,k10_lattice3(esk2_0,X1,X2),X3)
    | ~ r1_orders_2(esk2_0,X2,X3)
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_23,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_11])).

cnf(c_0_25,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_20,c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( k10_lattice3(esk2_0,X1,X2) = k10_lattice3(esk2_0,X3,X4)
    | ~ r1_orders_2(esk2_0,X2,esk1_4(esk2_0,X3,X4,k10_lattice3(esk2_0,X1,X2)))
    | ~ r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X3,X4,k10_lattice3(esk2_0,X1,X2)))
    | ~ r1_orders_2(esk2_0,X4,k10_lattice3(esk2_0,X1,X2))
    | ~ r1_orders_2(esk2_0,X3,k10_lattice3(esk2_0,X1,X2))
    | ~ m1_subset_1(esk1_4(esk2_0,X3,X4,k10_lattice3(esk2_0,X1,X2)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k10_lattice3(esk2_0,X1,X2),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X4,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_27,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_orders_2(X2,X3,esk1_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ v5_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_23,c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,k10_lattice3(esk2_0,X2,X1))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_29,plain,
    ( r1_orders_2(X1,X2,esk1_4(X1,X3,X2,X4))
    | X4 = k10_lattice3(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_30,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( k10_lattice3(esk2_0,X1,X2) = k10_lattice3(esk2_0,X2,X3)
    | ~ r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X2,X3,k10_lattice3(esk2_0,X1,X2)))
    | ~ r1_orders_2(esk2_0,X3,k10_lattice3(esk2_0,X1,X2))
    | ~ m1_subset_1(esk1_4(esk2_0,X2,X3,k10_lattice3(esk2_0,X1,X2)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k10_lattice3(esk2_0,X1,X2),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_16]),c_0_17]),c_0_18])]),c_0_28])).

cnf(c_0_32,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_orders_2(X2,X4,esk1_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ v5_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_29,c_0_7])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,k10_lattice3(esk2_0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),u1_struct_0(X1))
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
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_35,negated_conjecture,
    ( k10_lattice3(esk2_0,X1,X2) = k10_lattice3(esk2_0,X2,X1)
    | ~ m1_subset_1(esk1_4(esk2_0,X2,X1,k10_lattice3(esk2_0,X1,X2)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k10_lattice3(esk2_0,X1,X2),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_16]),c_0_17]),c_0_18])]),c_0_28]),c_0_33])).

cnf(c_0_36,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | m1_subset_1(esk1_4(X2,X3,X4,X1),u1_struct_0(X2))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ v5_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_34,c_0_7])).

cnf(c_0_37,negated_conjecture,
    ( k10_lattice3(esk2_0,X1,X2) = k10_lattice3(esk2_0,X2,X1)
    | ~ m1_subset_1(k10_lattice3(esk2_0,X1,X2),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_16]),c_0_17]),c_0_18])]),c_0_28]),c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k10_lattice3(esk2_0,esk3_0,esk4_0) != k10_lattice3(esk2_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( k10_lattice3(esk2_0,X1,X2) = k10_lattice3(esk2_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_11]),c_0_18])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:26:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.43  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.027 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(l26_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k10_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l26_lattice3)).
% 0.19/0.43  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.19/0.43  fof(dt_k10_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 0.19/0.43  fof(t13_lattice3, conjecture, ![X1]:(((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k10_lattice3(X1,X2,X3)=k10_lattice3(X1,X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_lattice3)).
% 0.19/0.43  fof(c_0_4, plain, ![X10, X11, X12, X13, X14]:((((r1_orders_2(X10,X11,X13)|X13!=k10_lattice3(X10,X11,X12)|~m1_subset_1(X13,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~v5_orders_2(X10)|~v1_lattice3(X10)|~l1_orders_2(X10)))&(r1_orders_2(X10,X12,X13)|X13!=k10_lattice3(X10,X11,X12)|~m1_subset_1(X13,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~v5_orders_2(X10)|~v1_lattice3(X10)|~l1_orders_2(X10))))&(~m1_subset_1(X14,u1_struct_0(X10))|(~r1_orders_2(X10,X11,X14)|~r1_orders_2(X10,X12,X14)|r1_orders_2(X10,X13,X14))|X13!=k10_lattice3(X10,X11,X12)|~m1_subset_1(X13,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~v5_orders_2(X10)|~v1_lattice3(X10)|~l1_orders_2(X10))))&((m1_subset_1(esk1_4(X10,X11,X12,X13),u1_struct_0(X10))|(~r1_orders_2(X10,X11,X13)|~r1_orders_2(X10,X12,X13))|X13=k10_lattice3(X10,X11,X12)|~m1_subset_1(X13,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~v5_orders_2(X10)|~v1_lattice3(X10)|~l1_orders_2(X10)))&(((r1_orders_2(X10,X11,esk1_4(X10,X11,X12,X13))|(~r1_orders_2(X10,X11,X13)|~r1_orders_2(X10,X12,X13))|X13=k10_lattice3(X10,X11,X12)|~m1_subset_1(X13,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~v5_orders_2(X10)|~v1_lattice3(X10)|~l1_orders_2(X10)))&(r1_orders_2(X10,X12,esk1_4(X10,X11,X12,X13))|(~r1_orders_2(X10,X11,X13)|~r1_orders_2(X10,X12,X13))|X13=k10_lattice3(X10,X11,X12)|~m1_subset_1(X13,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~v5_orders_2(X10)|~v1_lattice3(X10)|~l1_orders_2(X10))))&(~r1_orders_2(X10,X13,esk1_4(X10,X11,X12,X13))|(~r1_orders_2(X10,X11,X13)|~r1_orders_2(X10,X12,X13))|X13=k10_lattice3(X10,X11,X12)|~m1_subset_1(X13,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,u1_struct_0(X10))|(v2_struct_0(X10)|~v5_orders_2(X10)|~v1_lattice3(X10)|~l1_orders_2(X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).
% 0.19/0.43  fof(c_0_5, plain, ![X6]:(~l1_orders_2(X6)|(~v1_lattice3(X6)|~v2_struct_0(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.19/0.43  cnf(c_0_6, plain, (r1_orders_2(X2,X5,X1)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|X5!=k10_lattice3(X2,X3,X4)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v5_orders_2(X2)|~v1_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.43  cnf(c_0_7, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.43  fof(c_0_8, plain, ![X7, X8, X9]:(~l1_orders_2(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|m1_subset_1(k10_lattice3(X7,X8,X9),u1_struct_0(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).
% 0.19/0.43  fof(c_0_9, negated_conjecture, ~(![X1]:(((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k10_lattice3(X1,X2,X3)=k10_lattice3(X1,X3,X2))))), inference(assume_negation,[status(cth)],[t13_lattice3])).
% 0.19/0.43  cnf(c_0_10, plain, (r1_orders_2(X1,X2,X3)|X2!=k10_lattice3(X1,X4,X5)|~r1_orders_2(X1,X5,X3)|~r1_orders_2(X1,X4,X3)|~v5_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[c_0_6, c_0_7])).
% 0.19/0.43  cnf(c_0_11, plain, (m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.43  fof(c_0_12, negated_conjecture, (((v5_orders_2(esk2_0)&v1_lattice3(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&k10_lattice3(esk2_0,esk3_0,esk4_0)!=k10_lattice3(esk2_0,esk4_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.19/0.43  cnf(c_0_13, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X3!=k10_lattice3(X1,X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.43  cnf(c_0_14, plain, (X2=k10_lattice3(X1,X3,X4)|v2_struct_0(X1)|~r1_orders_2(X1,X2,esk1_4(X1,X3,X4,X2))|~r1_orders_2(X1,X3,X2)|~r1_orders_2(X1,X4,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.43  cnf(c_0_15, plain, (r1_orders_2(X1,k10_lattice3(X1,X2,X3),X4)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~v5_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_10]), c_0_11])).
% 0.19/0.43  cnf(c_0_16, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  cnf(c_0_17, negated_conjecture, (v1_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  cnf(c_0_18, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  cnf(c_0_19, plain, (r1_orders_2(X1,X2,X3)|X3!=k10_lattice3(X1,X4,X2)|~v5_orders_2(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[c_0_13, c_0_7])).
% 0.19/0.43  cnf(c_0_20, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X3!=k10_lattice3(X1,X2,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.43  cnf(c_0_21, plain, (X1=k10_lattice3(X2,X3,X4)|~r1_orders_2(X2,X1,esk1_4(X2,X3,X4,X1))|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~v5_orders_2(X2)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v1_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_14, c_0_7])).
% 0.19/0.43  cnf(c_0_22, negated_conjecture, (r1_orders_2(esk2_0,k10_lattice3(esk2_0,X1,X2),X3)|~r1_orders_2(esk2_0,X2,X3)|~r1_orders_2(esk2_0,X1,X3)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X3,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])])).
% 0.19/0.43  cnf(c_0_23, plain, (r1_orders_2(X1,X2,esk1_4(X1,X2,X3,X4))|X4=k10_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.43  cnf(c_0_24, plain, (r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))|~v5_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]), c_0_11])).
% 0.19/0.43  cnf(c_0_25, plain, (r1_orders_2(X1,X2,X3)|X3!=k10_lattice3(X1,X2,X4)|~v5_orders_2(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[c_0_20, c_0_7])).
% 0.19/0.43  cnf(c_0_26, negated_conjecture, (k10_lattice3(esk2_0,X1,X2)=k10_lattice3(esk2_0,X3,X4)|~r1_orders_2(esk2_0,X2,esk1_4(esk2_0,X3,X4,k10_lattice3(esk2_0,X1,X2)))|~r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X3,X4,k10_lattice3(esk2_0,X1,X2)))|~r1_orders_2(esk2_0,X4,k10_lattice3(esk2_0,X1,X2))|~r1_orders_2(esk2_0,X3,k10_lattice3(esk2_0,X1,X2))|~m1_subset_1(esk1_4(esk2_0,X3,X4,k10_lattice3(esk2_0,X1,X2)),u1_struct_0(esk2_0))|~m1_subset_1(k10_lattice3(esk2_0,X1,X2),u1_struct_0(esk2_0))|~m1_subset_1(X4,u1_struct_0(esk2_0))|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_16]), c_0_17]), c_0_18])])).
% 0.19/0.43  cnf(c_0_27, plain, (X1=k10_lattice3(X2,X3,X4)|r1_orders_2(X2,X3,esk1_4(X2,X3,X4,X1))|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~v5_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v1_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_23, c_0_7])).
% 0.19/0.43  cnf(c_0_28, negated_conjecture, (r1_orders_2(esk2_0,X1,k10_lattice3(esk2_0,X2,X1))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_16]), c_0_17]), c_0_18])])).
% 0.19/0.43  cnf(c_0_29, plain, (r1_orders_2(X1,X2,esk1_4(X1,X3,X2,X4))|X4=k10_lattice3(X1,X3,X2)|v2_struct_0(X1)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.43  cnf(c_0_30, plain, (r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))|~v5_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]), c_0_11])).
% 0.19/0.43  cnf(c_0_31, negated_conjecture, (k10_lattice3(esk2_0,X1,X2)=k10_lattice3(esk2_0,X2,X3)|~r1_orders_2(esk2_0,X1,esk1_4(esk2_0,X2,X3,k10_lattice3(esk2_0,X1,X2)))|~r1_orders_2(esk2_0,X3,k10_lattice3(esk2_0,X1,X2))|~m1_subset_1(esk1_4(esk2_0,X2,X3,k10_lattice3(esk2_0,X1,X2)),u1_struct_0(esk2_0))|~m1_subset_1(k10_lattice3(esk2_0,X1,X2),u1_struct_0(esk2_0))|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_16]), c_0_17]), c_0_18])]), c_0_28])).
% 0.19/0.43  cnf(c_0_32, plain, (X1=k10_lattice3(X2,X3,X4)|r1_orders_2(X2,X4,esk1_4(X2,X3,X4,X1))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|~v5_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~v1_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_29, c_0_7])).
% 0.19/0.43  cnf(c_0_33, negated_conjecture, (r1_orders_2(esk2_0,X1,k10_lattice3(esk2_0,X1,X2))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_16]), c_0_17]), c_0_18])])).
% 0.19/0.43  cnf(c_0_34, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),u1_struct_0(X1))|X4=k10_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X4)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.43  cnf(c_0_35, negated_conjecture, (k10_lattice3(esk2_0,X1,X2)=k10_lattice3(esk2_0,X2,X1)|~m1_subset_1(esk1_4(esk2_0,X2,X1,k10_lattice3(esk2_0,X1,X2)),u1_struct_0(esk2_0))|~m1_subset_1(k10_lattice3(esk2_0,X1,X2),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_16]), c_0_17]), c_0_18])]), c_0_28]), c_0_33])).
% 0.19/0.43  cnf(c_0_36, plain, (X1=k10_lattice3(X2,X3,X4)|m1_subset_1(esk1_4(X2,X3,X4,X1),u1_struct_0(X2))|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~v5_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v1_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_34, c_0_7])).
% 0.19/0.43  cnf(c_0_37, negated_conjecture, (k10_lattice3(esk2_0,X1,X2)=k10_lattice3(esk2_0,X2,X1)|~m1_subset_1(k10_lattice3(esk2_0,X1,X2),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_16]), c_0_17]), c_0_18])]), c_0_28]), c_0_33])).
% 0.19/0.43  cnf(c_0_38, negated_conjecture, (k10_lattice3(esk2_0,esk3_0,esk4_0)!=k10_lattice3(esk2_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  cnf(c_0_39, negated_conjecture, (k10_lattice3(esk2_0,X1,X2)=k10_lattice3(esk2_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_11]), c_0_18])])).
% 0.19/0.43  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 43
% 0.19/0.43  # Proof object clause steps            : 34
% 0.19/0.43  # Proof object formula steps           : 9
% 0.19/0.43  # Proof object conjectures             : 18
% 0.19/0.43  # Proof object clause conjectures      : 15
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 15
% 0.19/0.43  # Proof object initial formulas used   : 4
% 0.19/0.43  # Proof object generating inferences   : 12
% 0.19/0.43  # Proof object simplifying inferences  : 45
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 4
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 15
% 0.19/0.43  # Removed in clause preprocessing      : 0
% 0.19/0.43  # Initial clauses in saturation        : 15
% 0.19/0.43  # Processed clauses                    : 513
% 0.19/0.43  # ...of these trivial                  : 27
% 0.19/0.43  # ...subsumed                          : 353
% 0.19/0.43  # ...remaining for further processing  : 133
% 0.19/0.43  # Other redundant clauses eliminated   : 99
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 30
% 0.19/0.43  # Backward-rewritten                   : 0
% 0.19/0.43  # Generated clauses                    : 1711
% 0.19/0.43  # ...of the previous two non-trivial   : 1261
% 0.19/0.43  # Contextual simplify-reflections      : 30
% 0.19/0.43  # Paramodulations                      : 1601
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 110
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 88
% 0.19/0.43  #    Positive orientable unit clauses  : 5
% 0.19/0.43  #    Positive unorientable unit clauses: 0
% 0.19/0.43  #    Negative unit clauses             : 1
% 0.19/0.43  #    Non-unit-clauses                  : 82
% 0.19/0.43  # Current number of unprocessed clauses: 734
% 0.19/0.43  # ...number of literals in the above   : 7533
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 45
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 8516
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 1271
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 413
% 0.19/0.43  # Unit Clause-clause subsumption calls : 0
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 0
% 0.19/0.43  # BW rewrite match successes           : 0
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 78353
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.096 s
% 0.19/0.43  # System time              : 0.004 s
% 0.19/0.43  # Total time               : 0.101 s
% 0.19/0.43  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
