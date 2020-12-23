%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:57 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 295 expanded)
%              Number of clauses        :   45 ( 113 expanded)
%              Number of leaves         :    9 (  75 expanded)
%              Depth                    :   13
%              Number of atoms          :  530 (2533 expanded)
%              Number of equality atoms :   48 ( 241 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(dt_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k13_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k13_lattice3)).

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(t17_lattice3,axiom,(
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
             => k13_lattice3(X1,k12_lattice3(X1,X2,X3),X3) = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattice3)).

fof(dt_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_lattice3)).

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

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(c_0_9,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ( r1_orders_2(X16,X17,X19)
        | X19 != k10_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v1_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_orders_2(X16,X18,X19)
        | X19 != k10_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v1_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ m1_subset_1(X20,u1_struct_0(X16))
        | ~ r1_orders_2(X16,X17,X20)
        | ~ r1_orders_2(X16,X18,X20)
        | r1_orders_2(X16,X19,X20)
        | X19 != k10_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v1_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( m1_subset_1(esk1_4(X16,X17,X18,X19),u1_struct_0(X16))
        | ~ r1_orders_2(X16,X17,X19)
        | ~ r1_orders_2(X16,X18,X19)
        | X19 = k10_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v1_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_orders_2(X16,X17,esk1_4(X16,X17,X18,X19))
        | ~ r1_orders_2(X16,X17,X19)
        | ~ r1_orders_2(X16,X18,X19)
        | X19 = k10_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v1_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_orders_2(X16,X18,esk1_4(X16,X17,X18,X19))
        | ~ r1_orders_2(X16,X17,X19)
        | ~ r1_orders_2(X16,X18,X19)
        | X19 = k10_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v1_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ r1_orders_2(X16,X19,esk1_4(X16,X17,X18,X19))
        | ~ r1_orders_2(X16,X17,X19)
        | ~ r1_orders_2(X16,X18,X19)
        | X19 = k10_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v1_lattice3(X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).

fof(c_0_10,plain,(
    ! [X6] :
      ( ~ l1_orders_2(X6)
      | ~ v1_lattice3(X6)
      | ~ v2_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

fof(c_0_11,plain,(
    ! [X13,X14,X15] :
      ( ~ v5_orders_2(X13)
      | ~ v1_lattice3(X13)
      | ~ l1_orders_2(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | m1_subset_1(k13_lattice3(X13,X14,X15),u1_struct_0(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k13_lattice3])])).

fof(c_0_12,plain,(
    ! [X31,X32,X33] :
      ( ~ v5_orders_2(X31)
      | ~ v1_lattice3(X31)
      | ~ l1_orders_2(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | ~ m1_subset_1(X33,u1_struct_0(X31))
      | k13_lattice3(X31,X32,X33) = k10_lattice3(X31,X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

cnf(c_0_13,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( m1_subset_1(k13_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X3 != k10_lattice3(X1,X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | ~ r1_orders_2(X2,X1,esk1_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_22,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_orders_2(X2,X4,esk1_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_23,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k10_lattice3(X1,X4,X5)
    | ~ r1_orders_2(X1,X5,X3)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_24,plain,
    ( m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_19,c_0_14])).

cnf(c_0_26,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_20,c_0_14])).

cnf(c_0_27,plain,
    ( k10_lattice3(X1,X2,X3) = X3
    | ~ r1_orders_2(X1,X3,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( r1_orders_2(X1,k10_lattice3(X1,X2,X3),X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_24])).

cnf(c_0_29,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_24])).

cnf(c_0_30,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_24])).

cnf(c_0_31,plain,
    ( k10_lattice3(X1,X2,k10_lattice3(X1,X3,X4)) = k10_lattice3(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,k10_lattice3(X1,X3,X4))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_24]),c_0_29]),c_0_30])).

fof(c_0_32,plain,(
    ! [X34,X35,X36] :
      ( ~ v3_orders_2(X34)
      | ~ v5_orders_2(X34)
      | ~ v1_lattice3(X34)
      | ~ v2_lattice3(X34)
      | ~ l1_orders_2(X34)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | ~ m1_subset_1(X36,u1_struct_0(X34))
      | k13_lattice3(X34,k12_lattice3(X34,X35,X36),X36) = X36 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_lattice3])])])).

fof(c_0_33,plain,(
    ! [X10,X11,X12] :
      ( ~ v5_orders_2(X10)
      | ~ v2_lattice3(X10)
      | ~ l1_orders_2(X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | m1_subset_1(k12_lattice3(X10,X11,X12),u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k12_lattice3])])).

fof(c_0_34,negated_conjecture,(
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

cnf(c_0_35,plain,
    ( r1_orders_2(X1,k10_lattice3(X1,X2,X3),k10_lattice3(X1,X2,X3))
    | ~ r1_orders_2(X1,X4,k10_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_24])).

cnf(c_0_36,plain,
    ( k13_lattice3(X1,k12_lattice3(X1,X2,X3),X3) = X3
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_38,negated_conjecture,
    ( v3_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & v1_lattice3(esk3_0)
    & v2_lattice3(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & k12_lattice3(esk3_0,esk4_0,k13_lattice3(esk3_0,esk4_0,esk5_0)) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).

fof(c_0_39,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( ( r1_orders_2(X22,X25,X23)
        | X25 != k11_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v5_orders_2(X22)
        | ~ v2_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_orders_2(X22,X25,X24)
        | X25 != k11_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v5_orders_2(X22)
        | ~ v2_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ m1_subset_1(X26,u1_struct_0(X22))
        | ~ r1_orders_2(X22,X26,X23)
        | ~ r1_orders_2(X22,X26,X24)
        | r1_orders_2(X22,X26,X25)
        | X25 != k11_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v5_orders_2(X22)
        | ~ v2_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk2_4(X22,X23,X24,X25),u1_struct_0(X22))
        | ~ r1_orders_2(X22,X25,X23)
        | ~ r1_orders_2(X22,X25,X24)
        | X25 = k11_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v5_orders_2(X22)
        | ~ v2_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_orders_2(X22,esk2_4(X22,X23,X24,X25),X23)
        | ~ r1_orders_2(X22,X25,X23)
        | ~ r1_orders_2(X22,X25,X24)
        | X25 = k11_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v5_orders_2(X22)
        | ~ v2_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( r1_orders_2(X22,esk2_4(X22,X23,X24,X25),X24)
        | ~ r1_orders_2(X22,X25,X23)
        | ~ r1_orders_2(X22,X25,X24)
        | X25 = k11_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v5_orders_2(X22)
        | ~ v2_lattice3(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ r1_orders_2(X22,esk2_4(X22,X23,X24,X25),X25)
        | ~ r1_orders_2(X22,X25,X23)
        | ~ r1_orders_2(X22,X25,X24)
        | X25 = k11_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v5_orders_2(X22)
        | ~ v2_lattice3(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).

cnf(c_0_40,plain,
    ( r1_orders_2(X1,k10_lattice3(X1,X2,X3),k10_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_41,plain,
    ( k10_lattice3(X1,k12_lattice3(X1,X2,X3),X3) = X3
    | ~ v3_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_36]),c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( k12_lattice3(esk3_0,esk4_0,k13_lattice3(esk3_0,esk4_0,esk5_0)) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( v1_lattice3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_48,plain,(
    ! [X28,X29,X30] :
      ( ~ v5_orders_2(X28)
      | ~ v2_lattice3(X28)
      | ~ l1_orders_2(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | k12_lattice3(X28,X29,X30) = k11_lattice3(X28,X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

cnf(c_0_49,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( r1_orders_2(X1,esk2_4(X1,X2,X3,X4),X2)
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
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( v2_lattice3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( k12_lattice3(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0)) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_18]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_55,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( k11_lattice3(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X2)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_43]),c_0_52]),c_0_53]),c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_58,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_46]),c_0_47])])).

cnf(c_0_59,negated_conjecture,
    ( k11_lattice3(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0)) != esk4_0
    | ~ m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_53]),c_0_44]),c_0_45]),c_0_47])])).

cnf(c_0_60,negated_conjecture,
    ( k11_lattice3(esk3_0,X1,X2) = X1
    | ~ r1_orders_2(esk3_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_53]),c_0_45]),c_0_47])]),c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_orders_2(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_44])])).

cnf(c_0_62,negated_conjecture,
    ( ~ m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_29]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_24]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_S0Y
% 0.13/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.029 s
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(l26_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k10_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 0.13/0.40  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.13/0.40  fof(dt_k13_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k13_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k13_lattice3)).
% 0.13/0.40  fof(redefinition_k13_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 0.13/0.40  fof(t17_lattice3, axiom, ![X1]:(((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k13_lattice3(X1,k12_lattice3(X1,X2,X3),X3)=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_lattice3)).
% 0.13/0.40  fof(dt_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k12_lattice3)).
% 0.13/0.40  fof(t18_lattice3, conjecture, ![X1]:(((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k12_lattice3(X1,X2,k13_lattice3(X1,X2,X3))=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_lattice3)).
% 0.13/0.40  fof(l28_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k11_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 0.13/0.40  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.13/0.40  fof(c_0_9, plain, ![X16, X17, X18, X19, X20]:((((r1_orders_2(X16,X17,X19)|X19!=k10_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v1_lattice3(X16)|~l1_orders_2(X16)))&(r1_orders_2(X16,X18,X19)|X19!=k10_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v1_lattice3(X16)|~l1_orders_2(X16))))&(~m1_subset_1(X20,u1_struct_0(X16))|(~r1_orders_2(X16,X17,X20)|~r1_orders_2(X16,X18,X20)|r1_orders_2(X16,X19,X20))|X19!=k10_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v1_lattice3(X16)|~l1_orders_2(X16))))&((m1_subset_1(esk1_4(X16,X17,X18,X19),u1_struct_0(X16))|(~r1_orders_2(X16,X17,X19)|~r1_orders_2(X16,X18,X19))|X19=k10_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v1_lattice3(X16)|~l1_orders_2(X16)))&(((r1_orders_2(X16,X17,esk1_4(X16,X17,X18,X19))|(~r1_orders_2(X16,X17,X19)|~r1_orders_2(X16,X18,X19))|X19=k10_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v1_lattice3(X16)|~l1_orders_2(X16)))&(r1_orders_2(X16,X18,esk1_4(X16,X17,X18,X19))|(~r1_orders_2(X16,X17,X19)|~r1_orders_2(X16,X18,X19))|X19=k10_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v1_lattice3(X16)|~l1_orders_2(X16))))&(~r1_orders_2(X16,X19,esk1_4(X16,X17,X18,X19))|(~r1_orders_2(X16,X17,X19)|~r1_orders_2(X16,X18,X19))|X19=k10_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v1_lattice3(X16)|~l1_orders_2(X16)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).
% 0.13/0.40  fof(c_0_10, plain, ![X6]:(~l1_orders_2(X6)|(~v1_lattice3(X6)|~v2_struct_0(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.13/0.40  fof(c_0_11, plain, ![X13, X14, X15]:(~v5_orders_2(X13)|~v1_lattice3(X13)|~l1_orders_2(X13)|~m1_subset_1(X14,u1_struct_0(X13))|~m1_subset_1(X15,u1_struct_0(X13))|m1_subset_1(k13_lattice3(X13,X14,X15),u1_struct_0(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k13_lattice3])])).
% 0.13/0.40  fof(c_0_12, plain, ![X31, X32, X33]:(~v5_orders_2(X31)|~v1_lattice3(X31)|~l1_orders_2(X31)|~m1_subset_1(X32,u1_struct_0(X31))|~m1_subset_1(X33,u1_struct_0(X31))|k13_lattice3(X31,X32,X33)=k10_lattice3(X31,X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).
% 0.13/0.40  cnf(c_0_13, plain, (X2=k10_lattice3(X1,X3,X4)|v2_struct_0(X1)|~r1_orders_2(X1,X2,esk1_4(X1,X3,X4,X2))|~r1_orders_2(X1,X3,X2)|~r1_orders_2(X1,X4,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_14, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.40  cnf(c_0_15, plain, (r1_orders_2(X1,X2,esk1_4(X1,X3,X2,X4))|X4=k10_lattice3(X1,X3,X2)|v2_struct_0(X1)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_16, plain, (r1_orders_2(X2,X5,X1)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|X5!=k10_lattice3(X2,X3,X4)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v5_orders_2(X2)|~v1_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_17, plain, (m1_subset_1(k13_lattice3(X1,X2,X3),u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  cnf(c_0_18, plain, (k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_19, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X3!=k10_lattice3(X1,X2,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_20, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X3!=k10_lattice3(X1,X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_21, plain, (X1=k10_lattice3(X2,X3,X4)|~r1_orders_2(X2,X1,esk1_4(X2,X3,X4,X1))|~r1_orders_2(X2,X4,X1)|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v5_orders_2(X2)|~v1_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.40  cnf(c_0_22, plain, (X1=k10_lattice3(X2,X3,X4)|r1_orders_2(X2,X4,esk1_4(X2,X3,X4,X1))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~v5_orders_2(X2)|~v1_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_15, c_0_14])).
% 0.13/0.40  cnf(c_0_23, plain, (r1_orders_2(X1,X2,X3)|X2!=k10_lattice3(X1,X4,X5)|~r1_orders_2(X1,X5,X3)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[c_0_16, c_0_14])).
% 0.13/0.40  cnf(c_0_24, plain, (m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.40  cnf(c_0_25, plain, (r1_orders_2(X1,X2,X3)|X3!=k10_lattice3(X1,X2,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[c_0_19, c_0_14])).
% 0.13/0.40  cnf(c_0_26, plain, (r1_orders_2(X1,X2,X3)|X3!=k10_lattice3(X1,X4,X2)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[c_0_20, c_0_14])).
% 0.13/0.40  cnf(c_0_27, plain, (k10_lattice3(X1,X2,X3)=X3|~r1_orders_2(X1,X3,X3)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.40  cnf(c_0_28, plain, (r1_orders_2(X1,k10_lattice3(X1,X2,X3),X4)|~r1_orders_2(X1,X3,X4)|~r1_orders_2(X1,X2,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_23]), c_0_24])).
% 0.13/0.40  cnf(c_0_29, plain, (r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]), c_0_24])).
% 0.13/0.40  cnf(c_0_30, plain, (r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_26]), c_0_24])).
% 0.13/0.40  cnf(c_0_31, plain, (k10_lattice3(X1,X2,k10_lattice3(X1,X3,X4))=k10_lattice3(X1,X3,X4)|~r1_orders_2(X1,X2,k10_lattice3(X1,X3,X4))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_24]), c_0_29]), c_0_30])).
% 0.13/0.40  fof(c_0_32, plain, ![X34, X35, X36]:(~v3_orders_2(X34)|~v5_orders_2(X34)|~v1_lattice3(X34)|~v2_lattice3(X34)|~l1_orders_2(X34)|(~m1_subset_1(X35,u1_struct_0(X34))|(~m1_subset_1(X36,u1_struct_0(X34))|k13_lattice3(X34,k12_lattice3(X34,X35,X36),X36)=X36))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_lattice3])])])).
% 0.13/0.40  fof(c_0_33, plain, ![X10, X11, X12]:(~v5_orders_2(X10)|~v2_lattice3(X10)|~l1_orders_2(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))|m1_subset_1(k12_lattice3(X10,X11,X12),u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k12_lattice3])])).
% 0.13/0.40  fof(c_0_34, negated_conjecture, ~(![X1]:(((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k12_lattice3(X1,X2,k13_lattice3(X1,X2,X3))=X2)))), inference(assume_negation,[status(cth)],[t18_lattice3])).
% 0.13/0.40  cnf(c_0_35, plain, (r1_orders_2(X1,k10_lattice3(X1,X2,X3),k10_lattice3(X1,X2,X3))|~r1_orders_2(X1,X4,k10_lattice3(X1,X2,X3))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_24])).
% 0.13/0.40  cnf(c_0_36, plain, (k13_lattice3(X1,k12_lattice3(X1,X2,X3),X3)=X3|~v3_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.40  cnf(c_0_37, plain, (m1_subset_1(k12_lattice3(X1,X2,X3),u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.40  fof(c_0_38, negated_conjecture, (((((v3_orders_2(esk3_0)&v5_orders_2(esk3_0))&v1_lattice3(esk3_0))&v2_lattice3(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&k12_lattice3(esk3_0,esk4_0,k13_lattice3(esk3_0,esk4_0,esk5_0))!=esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).
% 0.13/0.40  fof(c_0_39, plain, ![X22, X23, X24, X25, X26]:((((r1_orders_2(X22,X25,X23)|X25!=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22)))&(r1_orders_2(X22,X25,X24)|X25!=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22))))&(~m1_subset_1(X26,u1_struct_0(X22))|(~r1_orders_2(X22,X26,X23)|~r1_orders_2(X22,X26,X24)|r1_orders_2(X22,X26,X25))|X25!=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22))))&((m1_subset_1(esk2_4(X22,X23,X24,X25),u1_struct_0(X22))|(~r1_orders_2(X22,X25,X23)|~r1_orders_2(X22,X25,X24))|X25=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22)))&(((r1_orders_2(X22,esk2_4(X22,X23,X24,X25),X23)|(~r1_orders_2(X22,X25,X23)|~r1_orders_2(X22,X25,X24))|X25=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22)))&(r1_orders_2(X22,esk2_4(X22,X23,X24,X25),X24)|(~r1_orders_2(X22,X25,X23)|~r1_orders_2(X22,X25,X24))|X25=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22))))&(~r1_orders_2(X22,esk2_4(X22,X23,X24,X25),X25)|(~r1_orders_2(X22,X25,X23)|~r1_orders_2(X22,X25,X24))|X25=k11_lattice3(X22,X23,X24)|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).
% 0.13/0.40  cnf(c_0_40, plain, (r1_orders_2(X1,k10_lattice3(X1,X2,X3),k10_lattice3(X1,X2,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_35, c_0_30])).
% 0.13/0.40  cnf(c_0_41, plain, (k10_lattice3(X1,k12_lattice3(X1,X2,X3),X3)=X3|~v3_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_36]), c_0_37])).
% 0.13/0.40  cnf(c_0_42, negated_conjecture, (k12_lattice3(esk3_0,esk4_0,k13_lattice3(esk3_0,esk4_0,esk5_0))!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_45, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_46, negated_conjecture, (v1_lattice3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  fof(c_0_48, plain, ![X28, X29, X30]:(~v5_orders_2(X28)|~v2_lattice3(X28)|~l1_orders_2(X28)|~m1_subset_1(X29,u1_struct_0(X28))|~m1_subset_1(X30,u1_struct_0(X28))|k12_lattice3(X28,X29,X30)=k11_lattice3(X28,X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.13/0.40  cnf(c_0_49, plain, (X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,esk2_4(X1,X2,X3,X4),X4)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.40  cnf(c_0_50, plain, (r1_orders_2(X1,esk2_4(X1,X2,X3,X4),X2)|X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.40  cnf(c_0_51, plain, (r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~v2_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_37])).
% 0.13/0.40  cnf(c_0_52, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (v2_lattice3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_54, negated_conjecture, (k12_lattice3(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0))!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_18]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])])).
% 0.13/0.40  cnf(c_0_55, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.40  cnf(c_0_56, plain, (k11_lattice3(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X2,X2)|~v2_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.40  cnf(c_0_57, negated_conjecture, (r1_orders_2(esk3_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_43]), c_0_52]), c_0_53]), c_0_45]), c_0_46]), c_0_47])])).
% 0.13/0.40  cnf(c_0_58, negated_conjecture, (~v2_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_46]), c_0_47])])).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, (k11_lattice3(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0))!=esk4_0|~m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_53]), c_0_44]), c_0_45]), c_0_47])])).
% 0.13/0.40  cnf(c_0_60, negated_conjecture, (k11_lattice3(esk3_0,X1,X2)=X1|~r1_orders_2(esk3_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_53]), c_0_45]), c_0_47])]), c_0_58])).
% 0.13/0.40  cnf(c_0_61, negated_conjecture, (~r1_orders_2(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0))|~m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_44])])).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, (~m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_29]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])])).
% 0.13/0.40  cnf(c_0_63, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_24]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 64
% 0.13/0.40  # Proof object clause steps            : 45
% 0.13/0.40  # Proof object formula steps           : 19
% 0.13/0.40  # Proof object conjectures             : 19
% 0.13/0.40  # Proof object clause conjectures      : 16
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 21
% 0.13/0.40  # Proof object initial formulas used   : 9
% 0.13/0.40  # Proof object generating inferences   : 19
% 0.13/0.40  # Proof object simplifying inferences  : 52
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 10
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 29
% 0.13/0.40  # Removed in clause preprocessing      : 0
% 0.13/0.40  # Initial clauses in saturation        : 29
% 0.13/0.40  # Processed clauses                    : 200
% 0.13/0.40  # ...of these trivial                  : 0
% 0.13/0.40  # ...subsumed                          : 102
% 0.13/0.40  # ...remaining for further processing  : 98
% 0.13/0.40  # Other redundant clauses eliminated   : 27
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 4
% 0.13/0.40  # Backward-rewritten                   : 0
% 0.13/0.40  # Generated clauses                    : 494
% 0.13/0.40  # ...of the previous two non-trivial   : 411
% 0.13/0.40  # Contextual simplify-reflections      : 44
% 0.13/0.40  # Paramodulations                      : 461
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 33
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 94
% 0.13/0.40  #    Positive orientable unit clauses  : 7
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 6
% 0.13/0.40  #    Non-unit-clauses                  : 81
% 0.13/0.40  # Current number of unprocessed clauses: 231
% 0.13/0.40  # ...number of literals in the above   : 2173
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 4
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 4171
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 284
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 147
% 0.13/0.40  # Unit Clause-clause subsumption calls : 22
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 0
% 0.13/0.40  # BW rewrite match successes           : 0
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 19952
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.053 s
% 0.13/0.40  # System time              : 0.006 s
% 0.13/0.40  # Total time               : 0.059 s
% 0.13/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
