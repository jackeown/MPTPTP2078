%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:56 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 183 expanded)
%              Number of clauses        :   36 (  63 expanded)
%              Number of leaves         :   10 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  443 (1377 expanded)
%              Number of equality atoms :   43 ( 146 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal clause size      :   74 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattice3)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(dt_k10_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(dt_k11_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(c_0_10,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( ( r1_orders_2(X17,X18,X20)
        | X20 != k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v5_orders_2(X17)
        | ~ v1_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X19,X20)
        | X20 != k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v5_orders_2(X17)
        | ~ v1_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X21,u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X21)
        | ~ r1_orders_2(X17,X19,X21)
        | r1_orders_2(X17,X20,X21)
        | X20 != k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v5_orders_2(X17)
        | ~ v1_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk1_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | X20 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v5_orders_2(X17)
        | ~ v1_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X18,esk1_4(X17,X18,X19,X20))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | X20 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v5_orders_2(X17)
        | ~ v1_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X19,esk1_4(X17,X18,X19,X20))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | X20 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v5_orders_2(X17)
        | ~ v1_lattice3(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,X20,esk1_4(X17,X18,X19,X20))
        | ~ r1_orders_2(X17,X18,X20)
        | ~ r1_orders_2(X17,X19,X20)
        | X20 = k10_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v5_orders_2(X17)
        | ~ v1_lattice3(X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).

fof(c_0_11,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | ~ v1_lattice3(X9)
      | ~ v2_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

fof(c_0_12,plain,(
    ! [X38,X39,X40] :
      ( ~ v3_orders_2(X38)
      | ~ v5_orders_2(X38)
      | ~ v1_lattice3(X38)
      | ~ v2_lattice3(X38)
      | ~ l1_orders_2(X38)
      | ~ m1_subset_1(X39,u1_struct_0(X38))
      | ~ m1_subset_1(X40,u1_struct_0(X38))
      | k13_lattice3(X38,k12_lattice3(X38,X39,X40),X40) = X40 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_lattice3])])])).

fof(c_0_13,plain,(
    ! [X29,X30,X31] :
      ( ~ v5_orders_2(X29)
      | ~ v2_lattice3(X29)
      | ~ l1_orders_2(X29)
      | ~ m1_subset_1(X30,u1_struct_0(X29))
      | ~ m1_subset_1(X31,u1_struct_0(X29))
      | k12_lattice3(X29,X30,X31) = k11_lattice3(X29,X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

cnf(c_0_14,plain,
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

cnf(c_0_15,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X11,X12,X13] :
      ( ~ l1_orders_2(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | ~ m1_subset_1(X13,u1_struct_0(X11))
      | m1_subset_1(k10_lattice3(X11,X12,X13),u1_struct_0(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).

fof(c_0_17,plain,(
    ! [X32,X33,X34] :
      ( ~ v5_orders_2(X32)
      | ~ v1_lattice3(X32)
      | ~ l1_orders_2(X32)
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | ~ m1_subset_1(X34,u1_struct_0(X32))
      | k13_lattice3(X32,X33,X34) = k10_lattice3(X32,X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

cnf(c_0_18,plain,
    ( k13_lattice3(X1,k12_lattice3(X1,X2,X3),X3) = X3
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X14,X15,X16] :
      ( ~ l1_orders_2(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | m1_subset_1(k11_lattice3(X14,X15,X16),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).

fof(c_0_21,negated_conjecture,(
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

fof(c_0_22,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ( r1_orders_2(X23,X26,X24)
        | X26 != k11_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v5_orders_2(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( r1_orders_2(X23,X26,X25)
        | X26 != k11_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v5_orders_2(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( ~ m1_subset_1(X27,u1_struct_0(X23))
        | ~ r1_orders_2(X23,X27,X24)
        | ~ r1_orders_2(X23,X27,X25)
        | r1_orders_2(X23,X27,X26)
        | X26 != k11_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v5_orders_2(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(esk2_4(X23,X24,X25,X26),u1_struct_0(X23))
        | ~ r1_orders_2(X23,X26,X24)
        | ~ r1_orders_2(X23,X26,X25)
        | X26 = k11_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v5_orders_2(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( r1_orders_2(X23,esk2_4(X23,X24,X25,X26),X24)
        | ~ r1_orders_2(X23,X26,X24)
        | ~ r1_orders_2(X23,X26,X25)
        | X26 = k11_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v5_orders_2(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( r1_orders_2(X23,esk2_4(X23,X24,X25,X26),X25)
        | ~ r1_orders_2(X23,X26,X24)
        | ~ r1_orders_2(X23,X26,X25)
        | X26 = k11_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v5_orders_2(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) )
      & ( ~ r1_orders_2(X23,esk2_4(X23,X24,X25,X26),X26)
        | ~ r1_orders_2(X23,X26,X24)
        | ~ r1_orders_2(X23,X26,X25)
        | X26 = k11_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v5_orders_2(X23)
        | ~ v2_lattice3(X23)
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).

fof(c_0_23,plain,(
    ! [X10] :
      ( ~ l1_orders_2(X10)
      | ~ v2_lattice3(X10)
      | ~ v2_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_24,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X4,X2)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_25,plain,
    ( m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k13_lattice3(X1,k11_lattice3(X1,X2,X3),X3) = X3
    | ~ v3_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,negated_conjecture,
    ( v3_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & v1_lattice3(esk3_0)
    & v2_lattice3(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & k12_lattice3(esk3_0,esk4_0,k13_lattice3(esk3_0,esk4_0,esk5_0)) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_30,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]),c_0_25])).

cnf(c_0_34,plain,
    ( k10_lattice3(X1,k11_lattice3(X1,X2,X3),X3) = X3
    | ~ v3_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( k12_lattice3(esk3_0,esk4_0,k13_lattice3(esk3_0,esk4_0,esk5_0)) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( v1_lattice3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | ~ v2_lattice3(X2)
    | ~ r1_orders_2(X2,esk2_4(X2,X3,X4,X1),X1)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_42,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | r1_orders_2(X2,esk2_4(X2,X3,X4,X1),X3)
    | ~ v2_lattice3(X2)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_43,plain,
    ( r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,negated_conjecture,
    ( v2_lattice3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,negated_conjecture,
    ( k12_lattice3(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0)) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_26]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_47,plain,
    ( k11_lattice3(X1,X2,X3) = X2
    | ~ v2_lattice3(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_37]),c_0_44]),c_0_45]),c_0_36]),c_0_39]),c_0_40])])).

cnf(c_0_49,plain,
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

cnf(c_0_50,negated_conjecture,
    ( k11_lattice3(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0)) != esk4_0
    | ~ m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_19]),c_0_45]),c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_51,negated_conjecture,
    ( k11_lattice3(esk3_0,X1,X2) = X1
    | ~ r1_orders_2(esk3_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_45]),c_0_39]),c_0_40])])).

cnf(c_0_52,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_49,c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_orders_2(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_38])])).

cnf(c_0_54,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]),c_0_25])).

cnf(c_0_55,negated_conjecture,
    ( ~ m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_25]),c_0_37]),c_0_38]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.29  % Computer   : n006.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.29  % CPULimit   : 60
% 0.10/0.29  % WCLimit    : 600
% 0.10/0.29  % DateTime   : Tue Dec  1 19:29:07 EST 2020
% 0.10/0.29  % CPUTime    : 
% 0.10/0.29  # Version: 2.5pre002
% 0.10/0.29  # No SInE strategy applied
% 0.10/0.29  # Trying AutoSched0 for 299 seconds
% 0.15/0.34  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_S0Y
% 0.15/0.34  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.15/0.34  #
% 0.15/0.34  # Preprocessing time       : 0.030 s
% 0.15/0.34  
% 0.15/0.34  # Proof found!
% 0.15/0.34  # SZS status Theorem
% 0.15/0.34  # SZS output start CNFRefutation
% 0.15/0.34  fof(l26_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k10_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l26_lattice3)).
% 0.15/0.34  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.15/0.34  fof(t17_lattice3, axiom, ![X1]:(((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k13_lattice3(X1,k12_lattice3(X1,X2,X3),X3)=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_lattice3)).
% 0.15/0.34  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.15/0.34  fof(dt_k10_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 0.15/0.34  fof(redefinition_k13_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 0.15/0.34  fof(dt_k11_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 0.15/0.34  fof(t18_lattice3, conjecture, ![X1]:(((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k12_lattice3(X1,X2,k13_lattice3(X1,X2,X3))=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_lattice3)).
% 0.15/0.34  fof(l28_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k11_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 0.15/0.34  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 0.15/0.34  fof(c_0_10, plain, ![X17, X18, X19, X20, X21]:((((r1_orders_2(X17,X18,X20)|X20!=k10_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v1_lattice3(X17)|~l1_orders_2(X17)))&(r1_orders_2(X17,X19,X20)|X20!=k10_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v1_lattice3(X17)|~l1_orders_2(X17))))&(~m1_subset_1(X21,u1_struct_0(X17))|(~r1_orders_2(X17,X18,X21)|~r1_orders_2(X17,X19,X21)|r1_orders_2(X17,X20,X21))|X20!=k10_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v1_lattice3(X17)|~l1_orders_2(X17))))&((m1_subset_1(esk1_4(X17,X18,X19,X20),u1_struct_0(X17))|(~r1_orders_2(X17,X18,X20)|~r1_orders_2(X17,X19,X20))|X20=k10_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v1_lattice3(X17)|~l1_orders_2(X17)))&(((r1_orders_2(X17,X18,esk1_4(X17,X18,X19,X20))|(~r1_orders_2(X17,X18,X20)|~r1_orders_2(X17,X19,X20))|X20=k10_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v1_lattice3(X17)|~l1_orders_2(X17)))&(r1_orders_2(X17,X19,esk1_4(X17,X18,X19,X20))|(~r1_orders_2(X17,X18,X20)|~r1_orders_2(X17,X19,X20))|X20=k10_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v1_lattice3(X17)|~l1_orders_2(X17))))&(~r1_orders_2(X17,X20,esk1_4(X17,X18,X19,X20))|(~r1_orders_2(X17,X18,X20)|~r1_orders_2(X17,X19,X20))|X20=k10_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v1_lattice3(X17)|~l1_orders_2(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).
% 0.15/0.34  fof(c_0_11, plain, ![X9]:(~l1_orders_2(X9)|(~v1_lattice3(X9)|~v2_struct_0(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.15/0.34  fof(c_0_12, plain, ![X38, X39, X40]:(~v3_orders_2(X38)|~v5_orders_2(X38)|~v1_lattice3(X38)|~v2_lattice3(X38)|~l1_orders_2(X38)|(~m1_subset_1(X39,u1_struct_0(X38))|(~m1_subset_1(X40,u1_struct_0(X38))|k13_lattice3(X38,k12_lattice3(X38,X39,X40),X40)=X40))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_lattice3])])])).
% 0.15/0.34  fof(c_0_13, plain, ![X29, X30, X31]:(~v5_orders_2(X29)|~v2_lattice3(X29)|~l1_orders_2(X29)|~m1_subset_1(X30,u1_struct_0(X29))|~m1_subset_1(X31,u1_struct_0(X29))|k12_lattice3(X29,X30,X31)=k11_lattice3(X29,X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.15/0.34  cnf(c_0_14, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X3!=k10_lattice3(X1,X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.34  cnf(c_0_15, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.34  fof(c_0_16, plain, ![X11, X12, X13]:(~l1_orders_2(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~m1_subset_1(X13,u1_struct_0(X11))|m1_subset_1(k10_lattice3(X11,X12,X13),u1_struct_0(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).
% 0.15/0.34  fof(c_0_17, plain, ![X32, X33, X34]:(~v5_orders_2(X32)|~v1_lattice3(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,u1_struct_0(X32))|~m1_subset_1(X34,u1_struct_0(X32))|k13_lattice3(X32,X33,X34)=k10_lattice3(X32,X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).
% 0.15/0.34  cnf(c_0_18, plain, (k13_lattice3(X1,k12_lattice3(X1,X2,X3),X3)=X3|~v3_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.34  cnf(c_0_19, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.34  fof(c_0_20, plain, ![X14, X15, X16]:(~l1_orders_2(X14)|~m1_subset_1(X15,u1_struct_0(X14))|~m1_subset_1(X16,u1_struct_0(X14))|m1_subset_1(k11_lattice3(X14,X15,X16),u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).
% 0.15/0.34  fof(c_0_21, negated_conjecture, ~(![X1]:(((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k12_lattice3(X1,X2,k13_lattice3(X1,X2,X3))=X2)))), inference(assume_negation,[status(cth)],[t18_lattice3])).
% 0.15/0.34  fof(c_0_22, plain, ![X23, X24, X25, X26, X27]:((((r1_orders_2(X23,X26,X24)|X26!=k11_lattice3(X23,X24,X25)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v5_orders_2(X23)|~v2_lattice3(X23)|~l1_orders_2(X23)))&(r1_orders_2(X23,X26,X25)|X26!=k11_lattice3(X23,X24,X25)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v5_orders_2(X23)|~v2_lattice3(X23)|~l1_orders_2(X23))))&(~m1_subset_1(X27,u1_struct_0(X23))|(~r1_orders_2(X23,X27,X24)|~r1_orders_2(X23,X27,X25)|r1_orders_2(X23,X27,X26))|X26!=k11_lattice3(X23,X24,X25)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v5_orders_2(X23)|~v2_lattice3(X23)|~l1_orders_2(X23))))&((m1_subset_1(esk2_4(X23,X24,X25,X26),u1_struct_0(X23))|(~r1_orders_2(X23,X26,X24)|~r1_orders_2(X23,X26,X25))|X26=k11_lattice3(X23,X24,X25)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v5_orders_2(X23)|~v2_lattice3(X23)|~l1_orders_2(X23)))&(((r1_orders_2(X23,esk2_4(X23,X24,X25,X26),X24)|(~r1_orders_2(X23,X26,X24)|~r1_orders_2(X23,X26,X25))|X26=k11_lattice3(X23,X24,X25)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v5_orders_2(X23)|~v2_lattice3(X23)|~l1_orders_2(X23)))&(r1_orders_2(X23,esk2_4(X23,X24,X25,X26),X25)|(~r1_orders_2(X23,X26,X24)|~r1_orders_2(X23,X26,X25))|X26=k11_lattice3(X23,X24,X25)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v5_orders_2(X23)|~v2_lattice3(X23)|~l1_orders_2(X23))))&(~r1_orders_2(X23,esk2_4(X23,X24,X25,X26),X26)|(~r1_orders_2(X23,X26,X24)|~r1_orders_2(X23,X26,X25))|X26=k11_lattice3(X23,X24,X25)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v5_orders_2(X23)|~v2_lattice3(X23)|~l1_orders_2(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).
% 0.15/0.34  fof(c_0_23, plain, ![X10]:(~l1_orders_2(X10)|(~v2_lattice3(X10)|~v2_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 0.15/0.34  cnf(c_0_24, plain, (r1_orders_2(X1,X2,X3)|X3!=k10_lattice3(X1,X4,X2)|~v1_lattice3(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)), inference(csr,[status(thm)],[c_0_14, c_0_15])).
% 0.15/0.34  cnf(c_0_25, plain, (m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.34  cnf(c_0_26, plain, (k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.34  cnf(c_0_27, plain, (k13_lattice3(X1,k11_lattice3(X1,X2,X3),X3)=X3|~v3_orders_2(X1)|~v2_lattice3(X1)|~v1_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.15/0.34  cnf(c_0_28, plain, (m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.34  fof(c_0_29, negated_conjecture, (((((v3_orders_2(esk3_0)&v5_orders_2(esk3_0))&v1_lattice3(esk3_0))&v2_lattice3(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&k12_lattice3(esk3_0,esk4_0,k13_lattice3(esk3_0,esk4_0,esk5_0))!=esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.15/0.34  cnf(c_0_30, plain, (X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,esk2_4(X1,X2,X3,X4),X4)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.15/0.34  cnf(c_0_31, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.15/0.34  cnf(c_0_32, plain, (r1_orders_2(X1,esk2_4(X1,X2,X3,X4),X2)|X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.15/0.34  cnf(c_0_33, plain, (r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))|~v1_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]), c_0_25])).
% 0.15/0.34  cnf(c_0_34, plain, (k10_lattice3(X1,k11_lattice3(X1,X2,X3),X3)=X3|~v3_orders_2(X1)|~v2_lattice3(X1)|~v1_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.15/0.34  cnf(c_0_35, negated_conjecture, (k12_lattice3(esk3_0,esk4_0,k13_lattice3(esk3_0,esk4_0,esk5_0))!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.15/0.34  cnf(c_0_36, negated_conjecture, (v1_lattice3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.15/0.34  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.15/0.34  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.15/0.34  cnf(c_0_39, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.15/0.34  cnf(c_0_40, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.15/0.34  cnf(c_0_41, plain, (X1=k11_lattice3(X2,X3,X4)|~v2_lattice3(X2)|~r1_orders_2(X2,esk2_4(X2,X3,X4,X1),X1)|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~l1_orders_2(X2)|~v5_orders_2(X2)), inference(csr,[status(thm)],[c_0_30, c_0_31])).
% 0.15/0.34  cnf(c_0_42, plain, (X1=k11_lattice3(X2,X3,X4)|r1_orders_2(X2,esk2_4(X2,X3,X4,X1),X3)|~v2_lattice3(X2)|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~l1_orders_2(X2)|~v5_orders_2(X2)), inference(csr,[status(thm)],[c_0_32, c_0_31])).
% 0.15/0.34  cnf(c_0_43, plain, (r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~v2_lattice3(X1)|~v1_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_28])).
% 0.15/0.34  cnf(c_0_44, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.15/0.34  cnf(c_0_45, negated_conjecture, (v2_lattice3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.15/0.34  cnf(c_0_46, negated_conjecture, (k12_lattice3(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0))!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_26]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])])).
% 0.15/0.34  cnf(c_0_47, plain, (k11_lattice3(X1,X2,X3)=X2|~v2_lattice3(X1)|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X2,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.15/0.34  cnf(c_0_48, negated_conjecture, (r1_orders_2(esk3_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_37]), c_0_44]), c_0_45]), c_0_36]), c_0_39]), c_0_40])])).
% 0.15/0.34  cnf(c_0_49, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X3!=k10_lattice3(X1,X2,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.34  cnf(c_0_50, negated_conjecture, (k11_lattice3(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0))!=esk4_0|~m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_19]), c_0_45]), c_0_38]), c_0_39]), c_0_40])])).
% 0.15/0.34  cnf(c_0_51, negated_conjecture, (k11_lattice3(esk3_0,X1,X2)=X1|~r1_orders_2(esk3_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_45]), c_0_39]), c_0_40])])).
% 0.15/0.34  cnf(c_0_52, plain, (r1_orders_2(X1,X2,X3)|X3!=k10_lattice3(X1,X2,X4)|~v1_lattice3(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)), inference(csr,[status(thm)],[c_0_49, c_0_15])).
% 0.15/0.34  cnf(c_0_53, negated_conjecture, (~r1_orders_2(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0))|~m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_38])])).
% 0.15/0.34  cnf(c_0_54, plain, (r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))|~v1_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]), c_0_25])).
% 0.15/0.34  cnf(c_0_55, negated_conjecture, (~m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])])).
% 0.15/0.34  cnf(c_0_56, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_25]), c_0_37]), c_0_38]), c_0_39])]), ['proof']).
% 0.15/0.34  # SZS output end CNFRefutation
% 0.15/0.34  # Proof object total steps             : 57
% 0.15/0.34  # Proof object clause steps            : 36
% 0.15/0.34  # Proof object formula steps           : 21
% 0.15/0.34  # Proof object conjectures             : 18
% 0.15/0.34  # Proof object clause conjectures      : 15
% 0.15/0.34  # Proof object formula conjectures     : 3
% 0.15/0.34  # Proof object initial clauses used    : 19
% 0.15/0.34  # Proof object initial formulas used   : 10
% 0.15/0.34  # Proof object generating inferences   : 13
% 0.15/0.34  # Proof object simplifying inferences  : 41
% 0.15/0.34  # Training examples: 0 positive, 0 negative
% 0.15/0.34  # Parsed axioms                        : 12
% 0.15/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.34  # Initial clauses                      : 31
% 0.15/0.34  # Removed in clause preprocessing      : 0
% 0.15/0.34  # Initial clauses in saturation        : 31
% 0.15/0.34  # Processed clauses                    : 136
% 0.15/0.34  # ...of these trivial                  : 0
% 0.15/0.34  # ...subsumed                          : 53
% 0.15/0.34  # ...remaining for further processing  : 83
% 0.15/0.34  # Other redundant clauses eliminated   : 24
% 0.15/0.34  # Clauses deleted for lack of memory   : 0
% 0.15/0.34  # Backward-subsumed                    : 4
% 0.15/0.34  # Backward-rewritten                   : 0
% 0.15/0.34  # Generated clauses                    : 245
% 0.15/0.34  # ...of the previous two non-trivial   : 188
% 0.15/0.34  # Contextual simplify-reflections      : 28
% 0.15/0.34  # Paramodulations                      : 215
% 0.15/0.34  # Factorizations                       : 0
% 0.15/0.34  # Equation resolutions                 : 30
% 0.15/0.34  # Propositional unsat checks           : 0
% 0.15/0.34  #    Propositional check models        : 0
% 0.15/0.34  #    Propositional check unsatisfiable : 0
% 0.15/0.34  #    Propositional clauses             : 0
% 0.15/0.34  #    Propositional clauses after purity: 0
% 0.15/0.34  #    Propositional unsat core size     : 0
% 0.15/0.34  #    Propositional preprocessing time  : 0.000
% 0.15/0.34  #    Propositional encoding time       : 0.000
% 0.15/0.34  #    Propositional solver time         : 0.000
% 0.15/0.34  #    Success case prop preproc time    : 0.000
% 0.15/0.34  #    Success case prop encoding time   : 0.000
% 0.15/0.34  #    Success case prop solver time     : 0.000
% 0.15/0.34  # Current number of processed clauses  : 79
% 0.15/0.34  #    Positive orientable unit clauses  : 7
% 0.15/0.34  #    Positive unorientable unit clauses: 0
% 0.15/0.34  #    Negative unit clauses             : 5
% 0.15/0.34  #    Non-unit-clauses                  : 67
% 0.15/0.34  # Current number of unprocessed clauses: 74
% 0.15/0.34  # ...number of literals in the above   : 595
% 0.15/0.34  # Current number of archived formulas  : 0
% 0.15/0.34  # Current number of archived clauses   : 4
% 0.15/0.34  # Clause-clause subsumption calls (NU) : 2103
% 0.15/0.34  # Rec. Clause-clause subsumption calls : 307
% 0.15/0.34  # Non-unit clause-clause subsumptions  : 83
% 0.15/0.34  # Unit Clause-clause subsumption calls : 15
% 0.15/0.34  # Rewrite failures with RHS unbound    : 0
% 0.15/0.34  # BW rewrite match attempts            : 0
% 0.15/0.34  # BW rewrite match successes           : 0
% 0.15/0.34  # Condensation attempts                : 0
% 0.15/0.34  # Condensation successes               : 0
% 0.15/0.34  # Termbank termtop insertions          : 11269
% 0.15/0.34  
% 0.15/0.34  # -------------------------------------------------
% 0.15/0.34  # User time                : 0.040 s
% 0.15/0.34  # System time              : 0.007 s
% 0.15/0.34  # Total time               : 0.047 s
% 0.15/0.34  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
