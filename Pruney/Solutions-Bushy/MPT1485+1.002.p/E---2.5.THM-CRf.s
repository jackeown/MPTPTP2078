%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1485+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:18 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  113 (6397 expanded)
%              Number of clauses        :   92 (2422 expanded)
%              Number of leaves         :   10 (1635 expanded)
%              Depth                    :   28
%              Number of atoms          : 1139 (74025 expanded)
%              Number of equality atoms :  113 (6378 expanded)
%              Maximal formula depth    :   47 (   8 average)
%              Maximal clause size      :  352 (   6 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(dt_k10_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

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

fof(d14_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v5_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( ? [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                      & r1_orders_2(X1,X4,X2)
                      & r1_orders_2(X1,X4,X3)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X5,X2)
                              & r1_orders_2(X1,X5,X3) )
                           => r1_orders_2(X1,X5,X4) ) ) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( X4 = k11_lattice3(X1,X2,X3)
                      <=> ( r1_orders_2(X1,X4,X2)
                          & r1_orders_2(X1,X4,X3)
                          & ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ( ( r1_orders_2(X1,X5,X2)
                                  & r1_orders_2(X1,X5,X3) )
                               => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_lattice3)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(commutativity_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k12_lattice3(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k12_lattice3)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

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

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(c_0_10,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( r1_orders_2(X21,X22,X24)
        | X24 != k10_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v5_orders_2(X21)
        | ~ v1_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_orders_2(X21,X23,X24)
        | X24 != k10_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v5_orders_2(X21)
        | ~ v1_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( ~ m1_subset_1(X25,u1_struct_0(X21))
        | ~ r1_orders_2(X21,X22,X25)
        | ~ r1_orders_2(X21,X23,X25)
        | r1_orders_2(X21,X24,X25)
        | X24 != k10_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v5_orders_2(X21)
        | ~ v1_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( m1_subset_1(esk3_4(X21,X22,X23,X24),u1_struct_0(X21))
        | ~ r1_orders_2(X21,X22,X24)
        | ~ r1_orders_2(X21,X23,X24)
        | X24 = k10_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v5_orders_2(X21)
        | ~ v1_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_orders_2(X21,X22,esk3_4(X21,X22,X23,X24))
        | ~ r1_orders_2(X21,X22,X24)
        | ~ r1_orders_2(X21,X23,X24)
        | X24 = k10_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v5_orders_2(X21)
        | ~ v1_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( r1_orders_2(X21,X23,esk3_4(X21,X22,X23,X24))
        | ~ r1_orders_2(X21,X22,X24)
        | ~ r1_orders_2(X21,X23,X24)
        | X24 = k10_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v5_orders_2(X21)
        | ~ v1_lattice3(X21)
        | ~ l1_orders_2(X21) )
      & ( ~ r1_orders_2(X21,X24,esk3_4(X21,X22,X23,X24))
        | ~ r1_orders_2(X21,X22,X24)
        | ~ r1_orders_2(X21,X23,X24)
        | X24 = k10_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v5_orders_2(X21)
        | ~ v1_lattice3(X21)
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).

fof(c_0_11,plain,(
    ! [X18,X19,X20] :
      ( ~ l1_orders_2(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | m1_subset_1(k10_lattice3(X18,X19,X20),u1_struct_0(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).

cnf(c_0_12,plain,
    ( X2 = k10_lattice3(X1,X3,X4)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,esk3_4(X1,X3,X4,X2))
    | ~ r1_orders_2(X1,X3,X2)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( r1_orders_2(X1,X2,esk3_4(X1,X3,X2,X4))
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
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X3 != k10_lattice3(X1,X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k10_lattice3(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ v1_lattice3(X1)
    | ~ r1_orders_2(X1,X3,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( r1_orders_2(X1,k10_lattice3(X1,X2,X3),X4)
    | v2_struct_0(X1)
    | ~ v1_lattice3(X1)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15])).

cnf(c_0_20,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_15])).

cnf(c_0_21,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))
    | v2_struct_0(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_15])).

cnf(c_0_22,plain,
    ( k10_lattice3(X1,X2,k10_lattice3(X1,X3,X4)) = k10_lattice3(X1,X3,X4)
    | v2_struct_0(X1)
    | ~ v1_lattice3(X1)
    | ~ r1_orders_2(X1,X2,k10_lattice3(X1,X3,X4))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_15]),c_0_20]),c_0_21])).

cnf(c_0_23,plain,
    ( r1_orders_2(X1,X2,esk3_4(X1,X2,X3,X4))
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
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
    ( r1_orders_2(X1,k10_lattice3(X1,X2,X3),k10_lattice3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ v1_lattice3(X1)
    | ~ r1_orders_2(X1,X4,k10_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_15])).

fof(c_0_25,negated_conjecture,(
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

cnf(c_0_26,plain,
    ( k10_lattice3(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ v1_lattice3(X1)
    | ~ r1_orders_2(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_23])).

cnf(c_0_27,plain,
    ( r1_orders_2(X1,k10_lattice3(X1,X2,X3),k10_lattice3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

fof(c_0_28,plain,(
    ! [X10,X11,X12,X13,X15,X16] :
      ( ( r1_orders_2(X10,X15,X11)
        | X15 != k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | m1_subset_1(esk1_4(X10,X11,X12,X13),u1_struct_0(X10))
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,X15,X12)
        | X15 != k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | m1_subset_1(esk1_4(X10,X11,X12,X13),u1_struct_0(X10))
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X16,X11)
        | ~ r1_orders_2(X10,X16,X12)
        | r1_orders_2(X10,X16,X15)
        | X15 != k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | m1_subset_1(esk1_4(X10,X11,X12,X13),u1_struct_0(X10))
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk2_4(X10,X11,X12,X15),u1_struct_0(X10))
        | ~ r1_orders_2(X10,X15,X11)
        | ~ r1_orders_2(X10,X15,X12)
        | X15 = k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | m1_subset_1(esk1_4(X10,X11,X12,X13),u1_struct_0(X10))
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,esk2_4(X10,X11,X12,X15),X11)
        | ~ r1_orders_2(X10,X15,X11)
        | ~ r1_orders_2(X10,X15,X12)
        | X15 = k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | m1_subset_1(esk1_4(X10,X11,X12,X13),u1_struct_0(X10))
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,esk2_4(X10,X11,X12,X15),X12)
        | ~ r1_orders_2(X10,X15,X11)
        | ~ r1_orders_2(X10,X15,X12)
        | X15 = k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | m1_subset_1(esk1_4(X10,X11,X12,X13),u1_struct_0(X10))
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,esk2_4(X10,X11,X12,X15),X15)
        | ~ r1_orders_2(X10,X15,X11)
        | ~ r1_orders_2(X10,X15,X12)
        | X15 = k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | m1_subset_1(esk1_4(X10,X11,X12,X13),u1_struct_0(X10))
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,X15,X11)
        | X15 != k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X11)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,X15,X12)
        | X15 != k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X11)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X16,X11)
        | ~ r1_orders_2(X10,X16,X12)
        | r1_orders_2(X10,X16,X15)
        | X15 != k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X11)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk2_4(X10,X11,X12,X15),u1_struct_0(X10))
        | ~ r1_orders_2(X10,X15,X11)
        | ~ r1_orders_2(X10,X15,X12)
        | X15 = k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X11)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,esk2_4(X10,X11,X12,X15),X11)
        | ~ r1_orders_2(X10,X15,X11)
        | ~ r1_orders_2(X10,X15,X12)
        | X15 = k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X11)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,esk2_4(X10,X11,X12,X15),X12)
        | ~ r1_orders_2(X10,X15,X11)
        | ~ r1_orders_2(X10,X15,X12)
        | X15 = k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X11)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,esk2_4(X10,X11,X12,X15),X15)
        | ~ r1_orders_2(X10,X15,X11)
        | ~ r1_orders_2(X10,X15,X12)
        | X15 = k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X11)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,X15,X11)
        | X15 != k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,X15,X12)
        | X15 != k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X16,X11)
        | ~ r1_orders_2(X10,X16,X12)
        | r1_orders_2(X10,X16,X15)
        | X15 != k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk2_4(X10,X11,X12,X15),u1_struct_0(X10))
        | ~ r1_orders_2(X10,X15,X11)
        | ~ r1_orders_2(X10,X15,X12)
        | X15 = k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,esk2_4(X10,X11,X12,X15),X11)
        | ~ r1_orders_2(X10,X15,X11)
        | ~ r1_orders_2(X10,X15,X12)
        | X15 = k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,esk2_4(X10,X11,X12,X15),X12)
        | ~ r1_orders_2(X10,X15,X11)
        | ~ r1_orders_2(X10,X15,X12)
        | X15 = k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,esk2_4(X10,X11,X12,X15),X15)
        | ~ r1_orders_2(X10,X15,X11)
        | ~ r1_orders_2(X10,X15,X12)
        | X15 = k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X12)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,X15,X11)
        | X15 != k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X13)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,X15,X12)
        | X15 != k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X13)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X16,X11)
        | ~ r1_orders_2(X10,X16,X12)
        | r1_orders_2(X10,X16,X15)
        | X15 != k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X13)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk2_4(X10,X11,X12,X15),u1_struct_0(X10))
        | ~ r1_orders_2(X10,X15,X11)
        | ~ r1_orders_2(X10,X15,X12)
        | X15 = k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X13)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,esk2_4(X10,X11,X12,X15),X11)
        | ~ r1_orders_2(X10,X15,X11)
        | ~ r1_orders_2(X10,X15,X12)
        | X15 = k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X13)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( r1_orders_2(X10,esk2_4(X10,X11,X12,X15),X12)
        | ~ r1_orders_2(X10,X15,X11)
        | ~ r1_orders_2(X10,X15,X12)
        | X15 = k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X13)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,esk2_4(X10,X11,X12,X15),X15)
        | ~ r1_orders_2(X10,X15,X11)
        | ~ r1_orders_2(X10,X15,X12)
        | X15 = k11_lattice3(X10,X11,X12)
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r1_orders_2(X10,esk1_4(X10,X11,X12,X13),X13)
        | ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r1_orders_2(X10,X13,X11)
        | ~ r1_orders_2(X10,X13,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v5_orders_2(X10)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_lattice3])])])])])).

fof(c_0_29,negated_conjecture,
    ( v3_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & v1_lattice3(esk4_0)
    & v2_lattice3(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & k12_lattice3(esk4_0,esk5_0,k13_lattice3(esk4_0,esk5_0,esk6_0)) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_30,plain,(
    ! [X27,X28,X29] :
      ( ~ v5_orders_2(X27)
      | ~ v2_lattice3(X27)
      | ~ l1_orders_2(X27)
      | ~ m1_subset_1(X28,u1_struct_0(X27))
      | ~ m1_subset_1(X29,u1_struct_0(X27))
      | k12_lattice3(X27,X28,X29) = k11_lattice3(X27,X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

fof(c_0_31,plain,(
    ! [X7,X8,X9] :
      ( ~ v5_orders_2(X7)
      | ~ v2_lattice3(X7)
      | ~ l1_orders_2(X7)
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | k12_lattice3(X7,X8,X9) = k12_lattice3(X7,X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k12_lattice3])])).

fof(c_0_32,plain,(
    ! [X6] :
      ( ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v2_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_33,plain,
    ( k10_lattice3(X1,k10_lattice3(X1,X2,X3),X4) = k10_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v1_lattice3(X1)
    | ~ r1_orders_2(X1,X4,k10_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_15])).

cnf(c_0_34,plain,
    ( r1_orders_2(X1,esk2_4(X1,X2,X3,X4),X2)
    | X4 = k11_lattice3(X1,X2,X3)
    | r1_orders_2(X1,esk1_4(X1,X2,X3,X5),X3)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X5,X2)
    | ~ r1_orders_2(X1,X5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r1_orders_2(X1,X2,X3)
    | r1_orders_2(X1,esk1_4(X1,X4,X3,X5),X3)
    | X2 != k11_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X5,X4)
    | ~ r1_orders_2(X1,X5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k12_lattice3(X1,X2,X3) = k12_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_41,plain,(
    ! [X36,X37,X38] :
      ( v2_struct_0(X36)
      | ~ v3_orders_2(X36)
      | ~ l1_orders_2(X36)
      | ~ m1_subset_1(X37,u1_struct_0(X36))
      | ~ m1_subset_1(X38,u1_struct_0(X36))
      | r3_orders_2(X36,X37,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

cnf(c_0_42,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( v2_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( k10_lattice3(X1,X2,X3) = k10_lattice3(X1,X4,X5)
    | v2_struct_0(X1)
    | ~ v1_lattice3(X1)
    | ~ r1_orders_2(X1,k10_lattice3(X1,X2,X3),k10_lattice3(X1,X4,X5))
    | ~ r1_orders_2(X1,k10_lattice3(X1,X4,X5),k10_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_33]),c_0_15]),c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( X1 = k11_lattice3(esk4_0,X2,X3)
    | r1_orders_2(esk4_0,esk1_4(esk4_0,X2,X3,esk5_0),X3)
    | r1_orders_2(esk4_0,esk2_4(esk4_0,X2,X3,X1),X2)
    | ~ r1_orders_2(esk4_0,esk5_0,X3)
    | ~ r1_orders_2(esk4_0,esk5_0,X2)
    | ~ r1_orders_2(esk4_0,X1,X3)
    | ~ r1_orders_2(esk4_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_46,plain,
    ( r1_orders_2(X1,X2,X3)
    | X2 != k11_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk1_4(X1,X4,X3,X5),X5)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X5,X4)
    | ~ r1_orders_2(X1,X5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_47,plain,
    ( r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X3)
    | r1_orders_2(X1,k11_lattice3(X1,X2,X3),X3)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_49,plain,(
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

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_52,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_37])])).

cnf(c_0_54,plain,
    ( k10_lattice3(X1,X2,X3) = k10_lattice3(X1,X4,X5)
    | v2_struct_0(X1)
    | ~ v1_lattice3(X1)
    | ~ r1_orders_2(X1,k10_lattice3(X1,X4,X5),k10_lattice3(X1,X2,X3))
    | ~ r1_orders_2(X1,X3,k10_lattice3(X1,X4,X5))
    | ~ r1_orders_2(X1,X2,k10_lattice3(X1,X4,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_19]),c_0_15])).

cnf(c_0_55,negated_conjecture,
    ( k11_lattice3(esk4_0,X1,X2) = esk5_0
    | r1_orders_2(esk4_0,esk2_4(esk4_0,X1,X2,esk5_0),X1)
    | r1_orders_2(esk4_0,esk1_4(esk4_0,X1,X2,esk5_0),X2)
    | ~ r1_orders_2(esk4_0,esk5_0,X2)
    | ~ r1_orders_2(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_35])).

cnf(c_0_56,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),X3)
    | r1_orders_2(X1,X4,X3)
    | X4 != k11_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2)
    | ~ r1_orders_2(X1,X3,X3)
    | ~ m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_48])).

cnf(c_0_58,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( r3_orders_2(esk4_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_37])]),c_0_53])).

cnf(c_0_60,plain,
    ( k10_lattice3(X1,X2,X3) = k10_lattice3(X1,X4,X5)
    | v2_struct_0(X1)
    | ~ v1_lattice3(X1)
    | ~ r1_orders_2(X1,X3,k10_lattice3(X1,X4,X5))
    | ~ r1_orders_2(X1,X2,k10_lattice3(X1,X4,X5))
    | ~ r1_orders_2(X1,X5,k10_lattice3(X1,X2,X3))
    | ~ r1_orders_2(X1,X4,k10_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_19]),c_0_15])).

cnf(c_0_61,plain,
    ( X4 = k11_lattice3(X1,X2,X3)
    | r1_orders_2(X1,esk1_4(X1,X2,X3,X5),X3)
    | ~ r1_orders_2(X1,esk2_4(X1,X2,X3,X4),X4)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X5,X2)
    | ~ r1_orders_2(X1,X5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_62,negated_conjecture,
    ( k11_lattice3(esk4_0,X1,esk5_0) = esk5_0
    | r1_orders_2(esk4_0,esk1_4(esk4_0,X1,esk5_0,esk5_0),esk5_0)
    | r1_orders_2(esk4_0,esk2_4(esk4_0,X1,esk5_0,esk5_0),X1)
    | ~ r1_orders_2(esk4_0,esk5_0,esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_35])).

cnf(c_0_63,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),X3)
    | ~ r1_orders_2(X1,X3,X2)
    | ~ r1_orders_2(X1,X3,X3)
    | ~ m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( k11_lattice3(esk4_0,X1,X2) = k11_lattice3(esk4_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_43]),c_0_36]),c_0_37])])).

cnf(c_0_65,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_52]),c_0_37])]),c_0_53])).

cnf(c_0_66,plain,
    ( k10_lattice3(X1,X2,X3) = k10_lattice3(X1,X4,X3)
    | v2_struct_0(X1)
    | ~ v1_lattice3(X1)
    | ~ r1_orders_2(X1,X2,k10_lattice3(X1,X4,X3))
    | ~ r1_orders_2(X1,X4,k10_lattice3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_21]),c_0_21])).

cnf(c_0_67,negated_conjecture,
    ( k11_lattice3(esk4_0,esk5_0,esk5_0) = esk5_0
    | r1_orders_2(esk4_0,esk1_4(esk4_0,esk5_0,esk5_0,esk5_0),esk5_0)
    | r1_orders_2(esk4_0,esk1_4(esk4_0,esk5_0,esk5_0,X1),esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk5_0)
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_68,negated_conjecture,
    ( r1_orders_2(esk4_0,k11_lattice3(esk4_0,X1,X2),X1)
    | ~ r1_orders_2(esk4_0,X1,X2)
    | ~ m1_subset_1(k11_lattice3(esk4_0,X1,X2),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_36]),c_0_37])]),c_0_65])).

cnf(c_0_69,plain,
    ( k10_lattice3(X1,X2,X2) = k10_lattice3(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v1_lattice3(X1)
    | ~ r1_orders_2(X1,X3,k10_lattice3(X1,X2,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_21])).

cnf(c_0_70,negated_conjecture,
    ( v1_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_71,negated_conjecture,
    ( k11_lattice3(esk4_0,esk5_0,esk5_0) = esk5_0
    | r1_orders_2(esk4_0,esk1_4(esk4_0,esk5_0,esk5_0,esk5_0),esk5_0)
    | r1_orders_2(esk4_0,esk1_4(esk4_0,esk5_0,esk5_0,X1),esk5_0)
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_65]),c_0_35])])).

cnf(c_0_72,negated_conjecture,
    ( r1_orders_2(esk4_0,k11_lattice3(esk4_0,X1,X2),X2)
    | ~ r1_orders_2(esk4_0,X2,X1)
    | ~ m1_subset_1(k11_lattice3(esk4_0,X1,X2),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( k10_lattice3(esk4_0,k10_lattice3(esk4_0,X1,X1),X1) = k10_lattice3(esk4_0,X1,X1)
    | ~ m1_subset_1(k10_lattice3(esk4_0,X1,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_65]),c_0_70]),c_0_36]),c_0_37])]),c_0_53])).

cnf(c_0_74,negated_conjecture,
    ( k10_lattice3(esk4_0,X1,X2) = X2
    | ~ r1_orders_2(esk4_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_65]),c_0_70]),c_0_36]),c_0_37])]),c_0_53])).

cnf(c_0_75,plain,
    ( X4 = k11_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk2_4(X1,X2,X3,X4),X4)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk1_4(X1,X2,X3,X5),X5)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X5,X2)
    | ~ r1_orders_2(X1,X5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_76,negated_conjecture,
    ( k11_lattice3(esk4_0,esk5_0,esk5_0) = esk5_0
    | r1_orders_2(esk4_0,esk1_4(esk4_0,esk5_0,esk5_0,esk5_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_35])).

cnf(c_0_77,plain,
    ( r1_orders_2(X1,esk2_4(X1,X2,X3,X4),X3)
    | X4 = k11_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk1_4(X1,X2,X3,X5),X5)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X5,X2)
    | ~ r1_orders_2(X1,X5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_78,negated_conjecture,
    ( k10_lattice3(esk4_0,k11_lattice3(esk4_0,X1,k10_lattice3(esk4_0,X2,X2)),X2) = k10_lattice3(esk4_0,X2,X2)
    | ~ r1_orders_2(esk4_0,k10_lattice3(esk4_0,X2,X2),X1)
    | ~ m1_subset_1(k11_lattice3(esk4_0,X1,k10_lattice3(esk4_0,X2,X2)),u1_struct_0(esk4_0))
    | ~ m1_subset_1(k10_lattice3(esk4_0,X2,X2),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_72]),c_0_70]),c_0_36]),c_0_37])]),c_0_53])).

cnf(c_0_79,negated_conjecture,
    ( k10_lattice3(esk4_0,X1,X1) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_65])).

cnf(c_0_80,negated_conjecture,
    ( k11_lattice3(esk4_0,esk5_0,esk5_0) = esk5_0
    | X1 = k11_lattice3(esk4_0,esk5_0,esk5_0)
    | ~ r1_orders_2(esk4_0,esk2_4(esk4_0,esk5_0,esk5_0,X1),X1)
    | ~ r1_orders_2(esk4_0,esk5_0,esk5_0)
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_81,negated_conjecture,
    ( k11_lattice3(esk4_0,esk5_0,esk5_0) = esk5_0
    | X1 = k11_lattice3(esk4_0,esk5_0,esk5_0)
    | r1_orders_2(esk4_0,esk2_4(esk4_0,esk5_0,esk5_0,X1),esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,esk5_0)
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_76]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_82,negated_conjecture,
    ( k10_lattice3(esk4_0,X1,X2) = X1
    | ~ r1_orders_2(esk4_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_65]),c_0_70]),c_0_36]),c_0_37])]),c_0_53])).

cnf(c_0_83,negated_conjecture,
    ( k10_lattice3(esk4_0,k11_lattice3(esk4_0,X1,X2),X2) = X2
    | ~ r1_orders_2(esk4_0,X2,X1)
    | ~ m1_subset_1(k11_lattice3(esk4_0,X1,X2),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( k11_lattice3(esk4_0,esk5_0,esk5_0) = esk5_0
    | ~ r1_orders_2(esk4_0,esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_35])])).

cnf(c_0_85,plain,
    ( k10_lattice3(X1,X2,X2) = k10_lattice3(X1,k10_lattice3(X1,X3,X4),X2)
    | v2_struct_0(X1)
    | ~ v1_lattice3(X1)
    | ~ r1_orders_2(X1,X4,k10_lattice3(X1,X2,X2))
    | ~ r1_orders_2(X1,X3,k10_lattice3(X1,X2,X2))
    | ~ m1_subset_1(k10_lattice3(X1,X2,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_19]),c_0_15])).

cnf(c_0_86,negated_conjecture,
    ( k10_lattice3(esk4_0,X1,X2) = X3
    | ~ r1_orders_2(esk4_0,X3,k10_lattice3(esk4_0,X1,X2))
    | ~ r1_orders_2(esk4_0,X1,X3)
    | ~ r1_orders_2(esk4_0,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_82]),c_0_70]),c_0_36]),c_0_37])]),c_0_53])).

cnf(c_0_87,negated_conjecture,
    ( k10_lattice3(esk4_0,esk5_0,esk5_0) = esk5_0
    | ~ r1_orders_2(esk4_0,esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_35])])).

cnf(c_0_88,negated_conjecture,
    ( k10_lattice3(esk4_0,k10_lattice3(esk4_0,X1,k10_lattice3(esk4_0,X2,X2)),X2) = k10_lattice3(esk4_0,X2,X2)
    | ~ r1_orders_2(esk4_0,X1,k10_lattice3(esk4_0,X2,X2))
    | ~ m1_subset_1(k10_lattice3(esk4_0,X2,X2),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_65]),c_0_70]),c_0_36]),c_0_37])]),c_0_53])).

cnf(c_0_89,negated_conjecture,
    ( esk5_0 = X1
    | ~ r1_orders_2(esk4_0,esk5_0,esk5_0)
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_35])])).

cnf(c_0_90,negated_conjecture,
    ( k10_lattice3(esk4_0,k10_lattice3(esk4_0,X1,X2),X2) = X2
    | ~ r1_orders_2(esk4_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_79])).

cnf(c_0_91,negated_conjecture,
    ( esk5_0 = X1
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_65]),c_0_35])])).

cnf(c_0_92,negated_conjecture,
    ( r1_orders_2(esk4_0,k10_lattice3(esk4_0,X1,X2),X2)
    | ~ r1_orders_2(esk4_0,X1,X2)
    | ~ m1_subset_1(k10_lattice3(esk4_0,X1,X2),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_90]),c_0_70]),c_0_36]),c_0_37])]),c_0_53])).

cnf(c_0_93,negated_conjecture,
    ( k10_lattice3(esk4_0,X1,esk5_0) = esk5_0
    | ~ r1_orders_2(esk4_0,esk5_0,k10_lattice3(esk4_0,X1,esk5_0))
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(k10_lattice3(esk4_0,X1,esk5_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_35])])).

cnf(c_0_94,plain,
    ( r1_orders_2(X1,esk2_4(X1,X2,X3,X4),X3)
    | X4 = k11_lattice3(X1,X2,X3)
    | r1_orders_2(X1,esk1_4(X1,X2,X3,X5),X3)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X5,X2)
    | ~ r1_orders_2(X1,X5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_95,negated_conjecture,
    ( k10_lattice3(esk4_0,X1,esk5_0) = esk5_0
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(k10_lattice3(esk4_0,X1,esk5_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_21]),c_0_70]),c_0_35]),c_0_36]),c_0_37])]),c_0_53])).

cnf(c_0_96,negated_conjecture,
    ( X1 = k11_lattice3(esk4_0,X2,X3)
    | r1_orders_2(esk4_0,esk1_4(esk4_0,X2,X3,esk5_0),X3)
    | r1_orders_2(esk4_0,esk2_4(esk4_0,X2,X3,X1),X3)
    | ~ r1_orders_2(esk4_0,esk5_0,X3)
    | ~ r1_orders_2(esk4_0,esk5_0,X2)
    | ~ r1_orders_2(esk4_0,X1,X3)
    | ~ r1_orders_2(esk4_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_97,negated_conjecture,
    ( k10_lattice3(esk4_0,X1,esk5_0) = esk5_0
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_15]),c_0_35]),c_0_37])])).

fof(c_0_98,plain,(
    ! [X30,X31,X32] :
      ( ~ v5_orders_2(X30)
      | ~ v1_lattice3(X30)
      | ~ l1_orders_2(X30)
      | ~ m1_subset_1(X31,u1_struct_0(X30))
      | ~ m1_subset_1(X32,u1_struct_0(X30))
      | k13_lattice3(X30,X31,X32) = k10_lattice3(X30,X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

cnf(c_0_99,negated_conjecture,
    ( k11_lattice3(esk4_0,X1,X2) = X2
    | r1_orders_2(esk4_0,esk1_4(esk4_0,X1,X2,esk5_0),X2)
    | r1_orders_2(esk4_0,esk1_4(esk4_0,X1,X2,X3),X2)
    | ~ r1_orders_2(esk4_0,esk5_0,X2)
    | ~ r1_orders_2(esk4_0,esk5_0,X1)
    | ~ r1_orders_2(esk4_0,X3,X2)
    | ~ r1_orders_2(esk4_0,X3,X1)
    | ~ r1_orders_2(esk4_0,X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_96]),c_0_36]),c_0_37])]),c_0_65])).

cnf(c_0_100,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk5_0)
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_97]),c_0_70]),c_0_35]),c_0_36]),c_0_37])]),c_0_53])).

cnf(c_0_101,negated_conjecture,
    ( k12_lattice3(esk4_0,esk5_0,k13_lattice3(esk4_0,esk5_0,esk6_0)) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_102,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( k11_lattice3(esk4_0,X1,X2) = X2
    | r1_orders_2(esk4_0,esk1_4(esk4_0,X1,X2,esk5_0),X2)
    | ~ r1_orders_2(esk4_0,esk5_0,X2)
    | ~ r1_orders_2(esk4_0,esk5_0,X1)
    | ~ r1_orders_2(esk4_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_35])).

cnf(c_0_104,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_65]),c_0_35])])).

cnf(c_0_105,negated_conjecture,
    ( k12_lattice3(esk4_0,esk5_0,k10_lattice3(esk4_0,esk5_0,esk6_0)) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_70]),c_0_51]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_106,negated_conjecture,
    ( k11_lattice3(esk4_0,X1,esk5_0) = esk5_0
    | X2 = k11_lattice3(esk4_0,X1,esk5_0)
    | ~ r1_orders_2(esk4_0,esk2_4(esk4_0,X1,esk5_0,X2),X2)
    | ~ r1_orders_2(esk4_0,esk5_0,X1)
    | ~ r1_orders_2(esk4_0,X2,esk5_0)
    | ~ r1_orders_2(esk4_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_103]),c_0_35]),c_0_36]),c_0_37])]),c_0_104])])).

cnf(c_0_107,negated_conjecture,
    ( k11_lattice3(esk4_0,X1,esk5_0) = esk5_0
    | X2 = k11_lattice3(esk4_0,X1,esk5_0)
    | r1_orders_2(esk4_0,esk2_4(esk4_0,X1,esk5_0,X2),esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,X1)
    | ~ r1_orders_2(esk4_0,X2,esk5_0)
    | ~ r1_orders_2(esk4_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_103]),c_0_35]),c_0_36]),c_0_37])]),c_0_104])])).

cnf(c_0_108,negated_conjecture,
    ( k11_lattice3(esk4_0,k10_lattice3(esk4_0,esk5_0,esk6_0),esk5_0) != esk5_0
    | ~ m1_subset_1(k10_lattice3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_48]),c_0_35]),c_0_36]),c_0_43]),c_0_37])])).

cnf(c_0_109,negated_conjecture,
    ( k11_lattice3(esk4_0,X1,esk5_0) = esk5_0
    | ~ r1_orders_2(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_104]),c_0_35])])).

cnf(c_0_110,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,esk5_0,k10_lattice3(esk4_0,esk5_0,esk6_0))
    | ~ m1_subset_1(k10_lattice3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_111,negated_conjecture,
    ( ~ m1_subset_1(k10_lattice3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_20]),c_0_70]),c_0_51]),c_0_35]),c_0_36]),c_0_37])]),c_0_53])).

cnf(c_0_112,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_15]),c_0_51]),c_0_35]),c_0_37])]),
    [proof]).

%------------------------------------------------------------------------------
