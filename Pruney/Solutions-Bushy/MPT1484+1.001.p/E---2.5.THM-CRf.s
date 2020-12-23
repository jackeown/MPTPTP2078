%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1484+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:18 EST 2020

% Result     : Theorem 1.32s
% Output     : CNFRefutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 589 expanded)
%              Number of clauses        :   60 ( 225 expanded)
%              Number of leaves         :    9 ( 149 expanded)
%              Depth                    :   17
%              Number of atoms          :  948 (7212 expanded)
%              Number of equality atoms :   83 ( 620 expanded)
%              Maximal formula depth    :   47 (   9 average)
%              Maximal clause size      :  352 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(dt_k11_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(t17_lattice3,conjecture,(
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

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(d13_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v5_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( ? [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                      & r1_orders_2(X1,X2,X4)
                      & r1_orders_2(X1,X3,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X2,X5)
                              & r1_orders_2(X1,X3,X5) )
                           => r1_orders_2(X1,X4,X5) ) ) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( X4 = k10_lattice3(X1,X2,X3)
                      <=> ( r1_orders_2(X1,X2,X4)
                          & r1_orders_2(X1,X3,X4)
                          & ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ( ( r1_orders_2(X1,X2,X5)
                                  & r1_orders_2(X1,X3,X5) )
                               => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattice3)).

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

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(c_0_9,plain,(
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
      & ( m1_subset_1(esk3_4(X21,X22,X23,X24),u1_struct_0(X21))
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
      & ( r1_orders_2(X21,esk3_4(X21,X22,X23,X24),X22)
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
      & ( r1_orders_2(X21,esk3_4(X21,X22,X23,X24),X23)
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
      & ( ~ r1_orders_2(X21,esk3_4(X21,X22,X23,X24),X24)
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

fof(c_0_10,plain,(
    ! [X6] :
      ( ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v2_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_11,plain,
    ( X4 = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,esk3_4(X1,X2,X3,X4),X4)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( r1_orders_2(X1,esk3_4(X1,X2,X3,X4),X3)
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_orders_2(X2,X1,X5)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ r1_orders_2(X2,X1,X4)
    | X5 != k11_lattice3(X2,X3,X4)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X15,X16,X17] :
      ( ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | m1_subset_1(k11_lattice3(X15,X16,X17),u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).

cnf(c_0_16,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k11_lattice3(X1,X3,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k11_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | ~ r1_orders_2(X2,esk3_4(X2,X3,X4,X1),X1)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | r1_orders_2(X2,esk3_4(X2,X3,X4,X1),X4)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_13,c_0_12])).

cnf(c_0_20,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k11_lattice3(X1,X4,X5)
    | ~ r1_orders_2(X1,X2,X5)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_14,c_0_12])).

cnf(c_0_21,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k11_lattice3(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_16,c_0_12])).

cnf(c_0_23,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k11_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_17,c_0_12])).

cnf(c_0_24,plain,
    ( k11_lattice3(X1,X2,X3) = X3
    | ~ r1_orders_2(X1,X3,X3)
    | ~ r1_orders_2(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( r1_orders_2(X1,X2,k11_lattice3(X1,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]),c_0_21])).

cnf(c_0_26,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_21])).

cnf(c_0_27,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_21])).

cnf(c_0_28,plain,
    ( r1_orders_2(X1,esk3_4(X1,X2,X3,X4),X2)
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,plain,
    ( k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4)) = k11_lattice3(X1,X3,X4)
    | ~ r1_orders_2(X1,k11_lattice3(X1,X3,X4),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_21]),c_0_26]),c_0_27])).

cnf(c_0_30,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | r1_orders_2(X2,esk3_4(X2,X3,X4,X1),X3)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_28,c_0_12])).

cnf(c_0_31,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),k11_lattice3(X1,X2,X3))
    | ~ r1_orders_2(X1,k11_lattice3(X1,X2,X3),X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_29]),c_0_21])).

fof(c_0_32,negated_conjecture,(
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
               => k13_lattice3(X1,k12_lattice3(X1,X2,X3),X3) = X3 ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_lattice3])).

cnf(c_0_33,plain,
    ( k11_lattice3(X1,X2,X3) = X2
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_30])).

cnf(c_0_34,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),k11_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_27])).

fof(c_0_35,plain,(
    ! [X36,X37,X38] :
      ( v2_struct_0(X36)
      | ~ v3_orders_2(X36)
      | ~ l1_orders_2(X36)
      | ~ m1_subset_1(X37,u1_struct_0(X36))
      | ~ m1_subset_1(X38,u1_struct_0(X36))
      | r3_orders_2(X36,X37,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_36,negated_conjecture,
    ( v3_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & v1_lattice3(esk4_0)
    & v2_lattice3(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & k13_lattice3(esk4_0,k12_lattice3(esk4_0,esk5_0,esk6_0),esk6_0) != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

cnf(c_0_37,plain,
    ( k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4) = k11_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,k11_lattice3(X1,X2,X3),X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_21])).

fof(c_0_38,plain,(
    ! [X7,X8,X9,X10,X12,X13] :
      ( ( r1_orders_2(X7,X8,X12)
        | X12 != k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | m1_subset_1(esk1_4(X7,X8,X9,X10),u1_struct_0(X7))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X9,X12)
        | X12 != k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | m1_subset_1(esk1_4(X7,X8,X9,X10),u1_struct_0(X7))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X13,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X13)
        | ~ r1_orders_2(X7,X9,X13)
        | r1_orders_2(X7,X12,X13)
        | X12 != k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | m1_subset_1(esk1_4(X7,X8,X9,X10),u1_struct_0(X7))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk2_4(X7,X8,X9,X12),u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X12)
        | ~ r1_orders_2(X7,X9,X12)
        | X12 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | m1_subset_1(esk1_4(X7,X8,X9,X10),u1_struct_0(X7))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X8,esk2_4(X7,X8,X9,X12))
        | ~ r1_orders_2(X7,X8,X12)
        | ~ r1_orders_2(X7,X9,X12)
        | X12 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | m1_subset_1(esk1_4(X7,X8,X9,X10),u1_struct_0(X7))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X9,esk2_4(X7,X8,X9,X12))
        | ~ r1_orders_2(X7,X8,X12)
        | ~ r1_orders_2(X7,X9,X12)
        | X12 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | m1_subset_1(esk1_4(X7,X8,X9,X10),u1_struct_0(X7))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,X12,esk2_4(X7,X8,X9,X12))
        | ~ r1_orders_2(X7,X8,X12)
        | ~ r1_orders_2(X7,X9,X12)
        | X12 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | m1_subset_1(esk1_4(X7,X8,X9,X10),u1_struct_0(X7))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X8,X12)
        | X12 != k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_orders_2(X7,X8,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X9,X12)
        | X12 != k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_orders_2(X7,X8,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X13,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X13)
        | ~ r1_orders_2(X7,X9,X13)
        | r1_orders_2(X7,X12,X13)
        | X12 != k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_orders_2(X7,X8,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk2_4(X7,X8,X9,X12),u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X12)
        | ~ r1_orders_2(X7,X9,X12)
        | X12 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_orders_2(X7,X8,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X8,esk2_4(X7,X8,X9,X12))
        | ~ r1_orders_2(X7,X8,X12)
        | ~ r1_orders_2(X7,X9,X12)
        | X12 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_orders_2(X7,X8,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X9,esk2_4(X7,X8,X9,X12))
        | ~ r1_orders_2(X7,X8,X12)
        | ~ r1_orders_2(X7,X9,X12)
        | X12 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_orders_2(X7,X8,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,X12,esk2_4(X7,X8,X9,X12))
        | ~ r1_orders_2(X7,X8,X12)
        | ~ r1_orders_2(X7,X9,X12)
        | X12 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_orders_2(X7,X8,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X8,X12)
        | X12 != k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_orders_2(X7,X9,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X9,X12)
        | X12 != k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_orders_2(X7,X9,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X13,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X13)
        | ~ r1_orders_2(X7,X9,X13)
        | r1_orders_2(X7,X12,X13)
        | X12 != k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_orders_2(X7,X9,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk2_4(X7,X8,X9,X12),u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X12)
        | ~ r1_orders_2(X7,X9,X12)
        | X12 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_orders_2(X7,X9,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X8,esk2_4(X7,X8,X9,X12))
        | ~ r1_orders_2(X7,X8,X12)
        | ~ r1_orders_2(X7,X9,X12)
        | X12 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_orders_2(X7,X9,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X9,esk2_4(X7,X8,X9,X12))
        | ~ r1_orders_2(X7,X8,X12)
        | ~ r1_orders_2(X7,X9,X12)
        | X12 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_orders_2(X7,X9,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,X12,esk2_4(X7,X8,X9,X12))
        | ~ r1_orders_2(X7,X8,X12)
        | ~ r1_orders_2(X7,X9,X12)
        | X12 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | r1_orders_2(X7,X9,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X8,X12)
        | X12 != k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X10,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X9,X12)
        | X12 != k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X10,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X13,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X13)
        | ~ r1_orders_2(X7,X9,X13)
        | r1_orders_2(X7,X12,X13)
        | X12 != k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X10,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk2_4(X7,X8,X9,X12),u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X12)
        | ~ r1_orders_2(X7,X9,X12)
        | X12 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X10,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X8,esk2_4(X7,X8,X9,X12))
        | ~ r1_orders_2(X7,X8,X12)
        | ~ r1_orders_2(X7,X9,X12)
        | X12 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X10,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,X9,esk2_4(X7,X8,X9,X12))
        | ~ r1_orders_2(X7,X8,X12)
        | ~ r1_orders_2(X7,X9,X12)
        | X12 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X10,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,X12,esk2_4(X7,X8,X9,X12))
        | ~ r1_orders_2(X7,X8,X12)
        | ~ r1_orders_2(X7,X9,X12)
        | X12 = k10_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X10,esk1_4(X7,X8,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X8,X10)
        | ~ r1_orders_2(X7,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v5_orders_2(X7)
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_lattice3])])])])])).

fof(c_0_39,plain,(
    ! [X33,X34,X35] :
      ( ( ~ r3_orders_2(X33,X34,X35)
        | r1_orders_2(X33,X34,X35)
        | v2_struct_0(X33)
        | ~ v3_orders_2(X33)
        | ~ l1_orders_2(X33)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | ~ m1_subset_1(X35,u1_struct_0(X33)) )
      & ( ~ r1_orders_2(X33,X34,X35)
        | r3_orders_2(X33,X34,X35)
        | v2_struct_0(X33)
        | ~ v3_orders_2(X33)
        | ~ l1_orders_2(X33)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | ~ m1_subset_1(X35,u1_struct_0(X33)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X4,X5)
    | ~ r1_orders_2(X1,k11_lattice3(X1,X4,X5),k11_lattice3(X1,X2,X3))
    | ~ r1_orders_2(X1,k11_lattice3(X1,X2,X3),k11_lattice3(X1,X4,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_37]),c_0_21]),c_0_21])).

cnf(c_0_45,plain,
    ( r1_orders_2(X1,X2,esk2_4(X1,X3,X2,X4))
    | X4 = k10_lattice3(X1,X3,X2)
    | r1_orders_2(X1,X2,esk1_4(X1,X3,X2,X5))
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X3,X5)
    | ~ r1_orders_2(X1,X2,X5)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( r3_orders_2(esk4_0,X1,X1)
    | v2_struct_0(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])])).

fof(c_0_49,plain,(
    ! [X27,X28,X29] :
      ( ~ v5_orders_2(X27)
      | ~ v2_lattice3(X27)
      | ~ l1_orders_2(X27)
      | ~ m1_subset_1(X28,u1_struct_0(X27))
      | ~ m1_subset_1(X29,u1_struct_0(X27))
      | k12_lattice3(X27,X28,X29) = k11_lattice3(X27,X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

cnf(c_0_50,plain,
    ( k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X4,X5)
    | ~ r1_orders_2(X1,k11_lattice3(X1,X2,X3),k11_lattice3(X1,X4,X5))
    | ~ r1_orders_2(X1,k11_lattice3(X1,X4,X5),X3)
    | ~ r1_orders_2(X1,k11_lattice3(X1,X4,X5),X2)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_25]),c_0_21])).

cnf(c_0_51,plain,
    ( X2 = k10_lattice3(X1,X3,X4)
    | r1_orders_2(X1,X4,esk1_4(X1,X3,X4,X5))
    | ~ r1_orders_2(X1,X2,esk2_4(X1,X3,X4,X2))
    | ~ r1_orders_2(X1,X3,X2)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X3,X5)
    | ~ r1_orders_2(X1,X4,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( X1 = k10_lattice3(esk4_0,X2,X3)
    | r1_orders_2(esk4_0,X3,esk1_4(esk4_0,X2,X3,esk6_0))
    | r1_orders_2(esk4_0,X3,esk2_4(esk4_0,X2,X3,X1))
    | ~ r1_orders_2(esk4_0,X2,esk6_0)
    | ~ r1_orders_2(esk4_0,X3,esk6_0)
    | ~ r1_orders_2(esk4_0,X2,X1)
    | ~ r1_orders_2(esk4_0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_41]),c_0_46]),c_0_43])])).

cnf(c_0_53,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,X1)
    | v2_struct_0(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_42]),c_0_43])])).

cnf(c_0_54,negated_conjecture,
    ( k13_lattice3(esk4_0,k12_lattice3(esk4_0,esk5_0,esk6_0),esk6_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_55,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( v2_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_58,plain,(
    ! [X30,X31,X32] :
      ( ~ v5_orders_2(X30)
      | ~ v1_lattice3(X30)
      | ~ l1_orders_2(X30)
      | ~ m1_subset_1(X31,u1_struct_0(X30))
      | ~ m1_subset_1(X32,u1_struct_0(X30))
      | k13_lattice3(X30,X31,X32) = k10_lattice3(X30,X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

cnf(c_0_59,plain,
    ( k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X4,X5)
    | ~ r1_orders_2(X1,k11_lattice3(X1,X4,X5),X3)
    | ~ r1_orders_2(X1,k11_lattice3(X1,X4,X5),X2)
    | ~ r1_orders_2(X1,k11_lattice3(X1,X2,X3),X5)
    | ~ r1_orders_2(X1,k11_lattice3(X1,X2,X3),X4)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_25]),c_0_21])).

cnf(c_0_60,negated_conjecture,
    ( k10_lattice3(esk4_0,X1,X2) = X2
    | r1_orders_2(esk4_0,X2,esk1_4(esk4_0,X1,X2,esk6_0))
    | r1_orders_2(esk4_0,X2,esk1_4(esk4_0,X1,X2,X3))
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ r1_orders_2(esk4_0,X2,esk6_0)
    | ~ r1_orders_2(esk4_0,X2,X3)
    | ~ r1_orders_2(esk4_0,X2,X2)
    | ~ r1_orders_2(esk4_0,X1,X3)
    | ~ r1_orders_2(esk4_0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_46]),c_0_43])])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk6_0)
    | v2_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_41])).

cnf(c_0_62,negated_conjecture,
    ( k13_lattice3(esk4_0,k11_lattice3(esk4_0,esk5_0,esk6_0),esk6_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_41]),c_0_56]),c_0_46]),c_0_57]),c_0_43])])).

cnf(c_0_63,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( v1_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_65,plain,
    ( k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X4)
    | ~ r1_orders_2(X1,k11_lattice3(X1,X3,X4),X2)
    | ~ r1_orders_2(X1,k11_lattice3(X1,X2,X3),X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_26]),c_0_27])).

cnf(c_0_66,plain,
    ( X2 = k10_lattice3(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,esk2_4(X1,X3,X4,X2))
    | ~ r1_orders_2(X1,X3,X2)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X5,esk1_4(X1,X3,X4,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X3,X5)
    | ~ r1_orders_2(X1,X4,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_67,negated_conjecture,
    ( k10_lattice3(esk4_0,X1,X2) = X2
    | r1_orders_2(esk4_0,X2,esk1_4(esk4_0,X1,X2,esk6_0))
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ r1_orders_2(esk4_0,X2,esk6_0)
    | ~ r1_orders_2(esk4_0,X2,X2)
    | ~ r1_orders_2(esk4_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_41])).

cnf(c_0_68,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_61]),c_0_57]),c_0_43])])).

cnf(c_0_69,plain,
    ( r1_orders_2(X1,X2,esk2_4(X1,X3,X2,X4))
    | X4 = k10_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X5,esk1_4(X1,X3,X2,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X3,X5)
    | ~ r1_orders_2(X1,X2,X5)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_70,negated_conjecture,
    ( k10_lattice3(esk4_0,k11_lattice3(esk4_0,esk5_0,esk6_0),esk6_0) != esk6_0
    | ~ m1_subset_1(k11_lattice3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_41]),c_0_46]),c_0_43])])).

cnf(c_0_71,plain,
    ( k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_27]),c_0_26])).

cnf(c_0_72,negated_conjecture,
    ( k10_lattice3(esk4_0,X1,esk6_0) = esk6_0
    | X2 = k10_lattice3(esk4_0,X1,esk6_0)
    | ~ r1_orders_2(esk4_0,X2,esk2_4(esk4_0,X1,esk6_0,X2))
    | ~ r1_orders_2(esk4_0,esk6_0,X2)
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ r1_orders_2(esk4_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_41]),c_0_46]),c_0_43])])).

cnf(c_0_73,negated_conjecture,
    ( k10_lattice3(esk4_0,X1,esk6_0) = esk6_0
    | X2 = k10_lattice3(esk4_0,X1,esk6_0)
    | r1_orders_2(esk4_0,esk6_0,esk2_4(esk4_0,X1,esk6_0,X2))
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ r1_orders_2(esk4_0,esk6_0,X2)
    | ~ r1_orders_2(esk4_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_67]),c_0_68]),c_0_41]),c_0_46]),c_0_43])])).

cnf(c_0_74,negated_conjecture,
    ( k10_lattice3(esk4_0,k11_lattice3(esk4_0,esk6_0,esk5_0),esk6_0) != esk6_0
    | ~ m1_subset_1(k11_lattice3(esk4_0,esk6_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_41]),c_0_56]),c_0_46]),c_0_57]),c_0_43])])).

cnf(c_0_75,negated_conjecture,
    ( k10_lattice3(esk4_0,X1,esk6_0) = esk6_0
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_68]),c_0_41])])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,k11_lattice3(esk4_0,esk6_0,esk5_0),esk6_0)
    | ~ m1_subset_1(k11_lattice3(esk4_0,esk6_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_77,negated_conjecture,
    ( ~ m1_subset_1(k11_lattice3(esk4_0,esk6_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_26]),c_0_56]),c_0_41]),c_0_46]),c_0_57]),c_0_43])])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_21]),c_0_56]),c_0_41]),c_0_43])]),
    [proof]).

%------------------------------------------------------------------------------
