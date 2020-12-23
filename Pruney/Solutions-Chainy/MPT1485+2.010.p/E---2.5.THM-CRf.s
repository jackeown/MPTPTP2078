%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:57 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 161 expanded)
%              Number of clauses        :   29 (  53 expanded)
%              Number of leaves         :    9 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :  372 (1159 expanded)
%              Number of equality atoms :   38 ( 127 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal clause size      :   74 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_lattice3,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k12_lattice3(X1,X2,k13_lattice3(X1,X2,X3)) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_lattice3)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(commutativity_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k12_lattice3(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k12_lattice3)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(l28_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k11_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X4,X2)
                      & r1_orders_2(X1,X4,X3)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X5,X2)
                              & r1_orders_2(X1,X5,X3) )
                           => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

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

fof(dt_k10_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k12_lattice3(X1,X2,k13_lattice3(X1,X2,X3)) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_lattice3])).

fof(c_0_10,plain,(
    ! [X8] :
      ( ~ l1_orders_2(X8)
      | ~ v1_lattice3(X8)
      | ~ v2_struct_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

fof(c_0_11,negated_conjecture,
    ( v3_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & v1_lattice3(esk3_0)
    & v2_lattice3(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & k12_lattice3(esk3_0,esk4_0,k13_lattice3(esk3_0,esk4_0,esk5_0)) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X30,X31,X32] :
      ( ~ v5_orders_2(X30)
      | ~ v1_lattice3(X30)
      | ~ l1_orders_2(X30)
      | ~ m1_subset_1(X31,u1_struct_0(X30))
      | ~ m1_subset_1(X32,u1_struct_0(X30))
      | k13_lattice3(X30,X31,X32) = k10_lattice3(X30,X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

fof(c_0_13,plain,(
    ! [X9,X10,X11] :
      ( ~ v5_orders_2(X9)
      | ~ v2_lattice3(X9)
      | ~ l1_orders_2(X9)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | k12_lattice3(X9,X10,X11) = k12_lattice3(X9,X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k12_lattice3])])).

fof(c_0_14,plain,(
    ! [X27,X28,X29] :
      ( ~ v5_orders_2(X27)
      | ~ v2_lattice3(X27)
      | ~ l1_orders_2(X27)
      | ~ m1_subset_1(X28,u1_struct_0(X27))
      | ~ m1_subset_1(X29,u1_struct_0(X27))
      | k12_lattice3(X27,X28,X29) = k11_lattice3(X27,X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

fof(c_0_15,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( r1_orders_2(X21,X24,X22)
        | X24 != k11_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v5_orders_2(X21)
        | ~ v2_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_orders_2(X21,X24,X23)
        | X24 != k11_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v5_orders_2(X21)
        | ~ v2_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( ~ m1_subset_1(X25,u1_struct_0(X21))
        | ~ r1_orders_2(X21,X25,X22)
        | ~ r1_orders_2(X21,X25,X23)
        | r1_orders_2(X21,X25,X24)
        | X24 != k11_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v5_orders_2(X21)
        | ~ v2_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( m1_subset_1(esk2_4(X21,X22,X23,X24),u1_struct_0(X21))
        | ~ r1_orders_2(X21,X24,X22)
        | ~ r1_orders_2(X21,X24,X23)
        | X24 = k11_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v5_orders_2(X21)
        | ~ v2_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_orders_2(X21,esk2_4(X21,X22,X23,X24),X22)
        | ~ r1_orders_2(X21,X24,X22)
        | ~ r1_orders_2(X21,X24,X23)
        | X24 = k11_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v5_orders_2(X21)
        | ~ v2_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_orders_2(X21,esk2_4(X21,X22,X23,X24),X23)
        | ~ r1_orders_2(X21,X24,X22)
        | ~ r1_orders_2(X21,X24,X23)
        | X24 = k11_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v5_orders_2(X21)
        | ~ v2_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( ~ r1_orders_2(X21,esk2_4(X21,X22,X23,X24),X24)
        | ~ r1_orders_2(X21,X24,X22)
        | ~ r1_orders_2(X21,X24,X23)
        | X24 = k11_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v5_orders_2(X21)
        | ~ v2_lattice3(X21)
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).

fof(c_0_16,plain,(
    ! [X6,X7] :
      ( v2_struct_0(X6)
      | ~ v3_orders_2(X6)
      | ~ l1_orders_2(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | r1_orders_2(X6,X7,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

cnf(c_0_17,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v1_lattice3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( k12_lattice3(esk3_0,esk4_0,k13_lattice3(esk3_0,esk4_0,esk5_0)) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( k12_lattice3(X1,X2,X3) = k12_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( X4 = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,esk2_4(X1,X2,X3,X4),X4)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
    ( r1_orders_2(X1,esk2_4(X1,X2,X3,X4),X3)
    | X4 = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

fof(c_0_32,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( r1_orders_2(X15,X16,X18)
        | X18 != k10_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v5_orders_2(X15)
        | ~ v1_lattice3(X15)
        | ~ l1_orders_2(X15) )
      & ( r1_orders_2(X15,X17,X18)
        | X18 != k10_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v5_orders_2(X15)
        | ~ v1_lattice3(X15)
        | ~ l1_orders_2(X15) )
      & ( ~ m1_subset_1(X19,u1_struct_0(X15))
        | ~ r1_orders_2(X15,X16,X19)
        | ~ r1_orders_2(X15,X17,X19)
        | r1_orders_2(X15,X18,X19)
        | X18 != k10_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v5_orders_2(X15)
        | ~ v1_lattice3(X15)
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk1_4(X15,X16,X17,X18),u1_struct_0(X15))
        | ~ r1_orders_2(X15,X16,X18)
        | ~ r1_orders_2(X15,X17,X18)
        | X18 = k10_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v5_orders_2(X15)
        | ~ v1_lattice3(X15)
        | ~ l1_orders_2(X15) )
      & ( r1_orders_2(X15,X16,esk1_4(X15,X16,X17,X18))
        | ~ r1_orders_2(X15,X16,X18)
        | ~ r1_orders_2(X15,X17,X18)
        | X18 = k10_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v5_orders_2(X15)
        | ~ v1_lattice3(X15)
        | ~ l1_orders_2(X15) )
      & ( r1_orders_2(X15,X17,esk1_4(X15,X16,X17,X18))
        | ~ r1_orders_2(X15,X16,X18)
        | ~ r1_orders_2(X15,X17,X18)
        | X18 = k10_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v5_orders_2(X15)
        | ~ v1_lattice3(X15)
        | ~ l1_orders_2(X15) )
      & ( ~ r1_orders_2(X15,X18,esk1_4(X15,X16,X17,X18))
        | ~ r1_orders_2(X15,X16,X18)
        | ~ r1_orders_2(X15,X17,X18)
        | X18 = k10_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v5_orders_2(X15)
        | ~ v1_lattice3(X15)
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).

cnf(c_0_33,negated_conjecture,
    ( k12_lattice3(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0)) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_18]),c_0_23]),c_0_24]),c_0_19])])).

cnf(c_0_34,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v2_lattice3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,plain,
    ( k11_lattice3(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,X3,X3)
    | ~ r1_orders_2(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_19])]),c_0_31])).

cnf(c_0_38,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X12,X13,X14] :
      ( ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | m1_subset_1(k10_lattice3(X12,X13,X14),u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).

cnf(c_0_40,negated_conjecture,
    ( k11_lattice3(esk3_0,k10_lattice3(esk3_0,esk4_0,esk5_0),esk4_0) != esk4_0
    | ~ m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_22]),c_0_24]),c_0_19])])).

cnf(c_0_41,negated_conjecture,
    ( k11_lattice3(esk3_0,X1,X2) = X2
    | ~ r1_orders_2(esk3_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_35]),c_0_22]),c_0_19])]),c_0_31])).

cnf(c_0_42,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_38,c_0_17])).

cnf(c_0_43,plain,
    ( m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_orders_2(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_24])])).

cnf(c_0_45,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_42]),c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( ~ m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_22]),c_0_18]),c_0_23]),c_0_24]),c_0_19])])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_43]),c_0_23]),c_0_24]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:50:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.37  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_S0Y
% 0.18/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.37  #
% 0.18/0.37  # Preprocessing time       : 0.030 s
% 0.18/0.37  
% 0.18/0.37  # Proof found!
% 0.18/0.37  # SZS status Theorem
% 0.18/0.37  # SZS output start CNFRefutation
% 0.18/0.37  fof(t18_lattice3, conjecture, ![X1]:(((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k12_lattice3(X1,X2,k13_lattice3(X1,X2,X3))=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_lattice3)).
% 0.18/0.37  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.18/0.37  fof(redefinition_k13_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 0.18/0.37  fof(commutativity_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k12_lattice3(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k12_lattice3)).
% 0.18/0.37  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.18/0.37  fof(l28_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k11_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 0.18/0.37  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 0.18/0.37  fof(l26_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k10_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 0.18/0.37  fof(dt_k10_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 0.18/0.37  fof(c_0_9, negated_conjecture, ~(![X1]:(((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k12_lattice3(X1,X2,k13_lattice3(X1,X2,X3))=X2)))), inference(assume_negation,[status(cth)],[t18_lattice3])).
% 0.18/0.37  fof(c_0_10, plain, ![X8]:(~l1_orders_2(X8)|(~v1_lattice3(X8)|~v2_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.18/0.37  fof(c_0_11, negated_conjecture, (((((v3_orders_2(esk3_0)&v5_orders_2(esk3_0))&v1_lattice3(esk3_0))&v2_lattice3(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&k12_lattice3(esk3_0,esk4_0,k13_lattice3(esk3_0,esk4_0,esk5_0))!=esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.18/0.37  fof(c_0_12, plain, ![X30, X31, X32]:(~v5_orders_2(X30)|~v1_lattice3(X30)|~l1_orders_2(X30)|~m1_subset_1(X31,u1_struct_0(X30))|~m1_subset_1(X32,u1_struct_0(X30))|k13_lattice3(X30,X31,X32)=k10_lattice3(X30,X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).
% 0.18/0.37  fof(c_0_13, plain, ![X9, X10, X11]:(~v5_orders_2(X9)|~v2_lattice3(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))|k12_lattice3(X9,X10,X11)=k12_lattice3(X9,X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k12_lattice3])])).
% 0.18/0.37  fof(c_0_14, plain, ![X27, X28, X29]:(~v5_orders_2(X27)|~v2_lattice3(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,u1_struct_0(X27))|~m1_subset_1(X29,u1_struct_0(X27))|k12_lattice3(X27,X28,X29)=k11_lattice3(X27,X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.18/0.37  fof(c_0_15, plain, ![X21, X22, X23, X24, X25]:((((r1_orders_2(X21,X24,X22)|X24!=k11_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v5_orders_2(X21)|~v2_lattice3(X21)|~l1_orders_2(X21)))&(r1_orders_2(X21,X24,X23)|X24!=k11_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v5_orders_2(X21)|~v2_lattice3(X21)|~l1_orders_2(X21))))&(~m1_subset_1(X25,u1_struct_0(X21))|(~r1_orders_2(X21,X25,X22)|~r1_orders_2(X21,X25,X23)|r1_orders_2(X21,X25,X24))|X24!=k11_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v5_orders_2(X21)|~v2_lattice3(X21)|~l1_orders_2(X21))))&((m1_subset_1(esk2_4(X21,X22,X23,X24),u1_struct_0(X21))|(~r1_orders_2(X21,X24,X22)|~r1_orders_2(X21,X24,X23))|X24=k11_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v5_orders_2(X21)|~v2_lattice3(X21)|~l1_orders_2(X21)))&(((r1_orders_2(X21,esk2_4(X21,X22,X23,X24),X22)|(~r1_orders_2(X21,X24,X22)|~r1_orders_2(X21,X24,X23))|X24=k11_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v5_orders_2(X21)|~v2_lattice3(X21)|~l1_orders_2(X21)))&(r1_orders_2(X21,esk2_4(X21,X22,X23,X24),X23)|(~r1_orders_2(X21,X24,X22)|~r1_orders_2(X21,X24,X23))|X24=k11_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v5_orders_2(X21)|~v2_lattice3(X21)|~l1_orders_2(X21))))&(~r1_orders_2(X21,esk2_4(X21,X22,X23,X24),X24)|(~r1_orders_2(X21,X24,X22)|~r1_orders_2(X21,X24,X23))|X24=k11_lattice3(X21,X22,X23)|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v5_orders_2(X21)|~v2_lattice3(X21)|~l1_orders_2(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).
% 0.18/0.37  fof(c_0_16, plain, ![X6, X7]:(v2_struct_0(X6)|~v3_orders_2(X6)|~l1_orders_2(X6)|(~m1_subset_1(X7,u1_struct_0(X6))|r1_orders_2(X6,X7,X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.18/0.37  cnf(c_0_17, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.37  cnf(c_0_18, negated_conjecture, (v1_lattice3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_19, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_20, negated_conjecture, (k12_lattice3(esk3_0,esk4_0,k13_lattice3(esk3_0,esk4_0,esk5_0))!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_21, plain, (k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.37  cnf(c_0_22, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_25, plain, (k12_lattice3(X1,X2,X3)=k12_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.37  cnf(c_0_26, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.37  cnf(c_0_27, plain, (X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,esk2_4(X1,X2,X3,X4),X4)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_28, plain, (r1_orders_2(X1,esk2_4(X1,X2,X3,X4),X3)|X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_29, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.37  cnf(c_0_30, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.18/0.37  fof(c_0_32, plain, ![X15, X16, X17, X18, X19]:((((r1_orders_2(X15,X16,X18)|X18!=k10_lattice3(X15,X16,X17)|~m1_subset_1(X18,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~v5_orders_2(X15)|~v1_lattice3(X15)|~l1_orders_2(X15)))&(r1_orders_2(X15,X17,X18)|X18!=k10_lattice3(X15,X16,X17)|~m1_subset_1(X18,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~v5_orders_2(X15)|~v1_lattice3(X15)|~l1_orders_2(X15))))&(~m1_subset_1(X19,u1_struct_0(X15))|(~r1_orders_2(X15,X16,X19)|~r1_orders_2(X15,X17,X19)|r1_orders_2(X15,X18,X19))|X18!=k10_lattice3(X15,X16,X17)|~m1_subset_1(X18,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~v5_orders_2(X15)|~v1_lattice3(X15)|~l1_orders_2(X15))))&((m1_subset_1(esk1_4(X15,X16,X17,X18),u1_struct_0(X15))|(~r1_orders_2(X15,X16,X18)|~r1_orders_2(X15,X17,X18))|X18=k10_lattice3(X15,X16,X17)|~m1_subset_1(X18,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~v5_orders_2(X15)|~v1_lattice3(X15)|~l1_orders_2(X15)))&(((r1_orders_2(X15,X16,esk1_4(X15,X16,X17,X18))|(~r1_orders_2(X15,X16,X18)|~r1_orders_2(X15,X17,X18))|X18=k10_lattice3(X15,X16,X17)|~m1_subset_1(X18,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~v5_orders_2(X15)|~v1_lattice3(X15)|~l1_orders_2(X15)))&(r1_orders_2(X15,X17,esk1_4(X15,X16,X17,X18))|(~r1_orders_2(X15,X16,X18)|~r1_orders_2(X15,X17,X18))|X18=k10_lattice3(X15,X16,X17)|~m1_subset_1(X18,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~v5_orders_2(X15)|~v1_lattice3(X15)|~l1_orders_2(X15))))&(~r1_orders_2(X15,X18,esk1_4(X15,X16,X17,X18))|(~r1_orders_2(X15,X16,X18)|~r1_orders_2(X15,X17,X18))|X18=k10_lattice3(X15,X16,X17)|~m1_subset_1(X18,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~v5_orders_2(X15)|~v1_lattice3(X15)|~l1_orders_2(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).
% 0.18/0.37  cnf(c_0_33, negated_conjecture, (k12_lattice3(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0))!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_18]), c_0_23]), c_0_24]), c_0_19])])).
% 0.18/0.37  cnf(c_0_34, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)|~v2_lattice3(X1)|~v5_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.37  cnf(c_0_35, negated_conjecture, (v2_lattice3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_36, plain, (k11_lattice3(X1,X2,X3)=X3|v2_struct_0(X1)|~v2_lattice3(X1)|~v5_orders_2(X1)|~r1_orders_2(X1,X3,X3)|~r1_orders_2(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.18/0.37  cnf(c_0_37, negated_conjecture, (r1_orders_2(esk3_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_19])]), c_0_31])).
% 0.18/0.37  cnf(c_0_38, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X3!=k10_lattice3(X1,X2,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.37  fof(c_0_39, plain, ![X12, X13, X14]:(~l1_orders_2(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))|m1_subset_1(k10_lattice3(X12,X13,X14),u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).
% 0.18/0.37  cnf(c_0_40, negated_conjecture, (k11_lattice3(esk3_0,k10_lattice3(esk3_0,esk4_0,esk5_0),esk4_0)!=esk4_0|~m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_22]), c_0_24]), c_0_19])])).
% 0.18/0.37  cnf(c_0_41, negated_conjecture, (k11_lattice3(esk3_0,X1,X2)=X2|~r1_orders_2(esk3_0,X2,X1)|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_35]), c_0_22]), c_0_19])]), c_0_31])).
% 0.18/0.37  cnf(c_0_42, plain, (r1_orders_2(X1,X2,X3)|X3!=k10_lattice3(X1,X2,X4)|~v5_orders_2(X1)|~v1_lattice3(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[c_0_38, c_0_17])).
% 0.18/0.37  cnf(c_0_43, plain, (m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.37  cnf(c_0_44, negated_conjecture, (~r1_orders_2(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0))|~m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_24])])).
% 0.18/0.37  cnf(c_0_45, plain, (r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))|~v5_orders_2(X1)|~v1_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_42]), c_0_43])).
% 0.18/0.37  cnf(c_0_46, negated_conjecture, (~m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_22]), c_0_18]), c_0_23]), c_0_24]), c_0_19])])).
% 0.18/0.37  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_43]), c_0_23]), c_0_24]), c_0_19])]), ['proof']).
% 0.18/0.37  # SZS output end CNFRefutation
% 0.18/0.37  # Proof object total steps             : 48
% 0.18/0.37  # Proof object clause steps            : 29
% 0.18/0.37  # Proof object formula steps           : 19
% 0.18/0.37  # Proof object conjectures             : 19
% 0.18/0.37  # Proof object clause conjectures      : 16
% 0.18/0.37  # Proof object formula conjectures     : 3
% 0.18/0.37  # Proof object initial clauses used    : 17
% 0.18/0.37  # Proof object initial formulas used   : 9
% 0.18/0.37  # Proof object generating inferences   : 11
% 0.18/0.37  # Proof object simplifying inferences  : 35
% 0.18/0.37  # Training examples: 0 positive, 0 negative
% 0.18/0.37  # Parsed axioms                        : 9
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 28
% 0.18/0.37  # Removed in clause preprocessing      : 0
% 0.18/0.37  # Initial clauses in saturation        : 28
% 0.18/0.37  # Processed clauses                    : 100
% 0.18/0.37  # ...of these trivial                  : 0
% 0.18/0.37  # ...subsumed                          : 38
% 0.18/0.37  # ...remaining for further processing  : 62
% 0.18/0.37  # Other redundant clauses eliminated   : 12
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 0
% 0.18/0.37  # Backward-rewritten                   : 0
% 0.18/0.37  # Generated clauses                    : 145
% 0.18/0.37  # ...of the previous two non-trivial   : 114
% 0.18/0.37  # Contextual simplify-reflections      : 10
% 0.18/0.37  # Paramodulations                      : 127
% 0.18/0.37  # Factorizations                       : 0
% 0.18/0.37  # Equation resolutions                 : 18
% 0.18/0.37  # Propositional unsat checks           : 0
% 0.18/0.37  #    Propositional check models        : 0
% 0.18/0.37  #    Propositional check unsatisfiable : 0
% 0.18/0.37  #    Propositional clauses             : 0
% 0.18/0.37  #    Propositional clauses after purity: 0
% 0.18/0.37  #    Propositional unsat core size     : 0
% 0.18/0.37  #    Propositional preprocessing time  : 0.000
% 0.18/0.37  #    Propositional encoding time       : 0.000
% 0.18/0.37  #    Propositional solver time         : 0.000
% 0.18/0.37  #    Success case prop preproc time    : 0.000
% 0.18/0.37  #    Success case prop encoding time   : 0.000
% 0.18/0.37  #    Success case prop solver time     : 0.000
% 0.18/0.37  # Current number of processed clauses  : 62
% 0.18/0.37  #    Positive orientable unit clauses  : 7
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 5
% 0.18/0.37  #    Non-unit-clauses                  : 50
% 0.18/0.37  # Current number of unprocessed clauses: 40
% 0.18/0.37  # ...number of literals in the above   : 299
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 0
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 950
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 146
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 44
% 0.18/0.37  # Unit Clause-clause subsumption calls : 12
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 0
% 0.18/0.37  # BW rewrite match successes           : 0
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 7422
% 0.18/0.38  
% 0.18/0.38  # -------------------------------------------------
% 0.18/0.38  # User time                : 0.039 s
% 0.18/0.38  # System time              : 0.004 s
% 0.18/0.38  # Total time               : 0.043 s
% 0.18/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
