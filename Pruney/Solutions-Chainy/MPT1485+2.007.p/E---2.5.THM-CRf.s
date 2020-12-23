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
% DateTime   : Thu Dec  3 11:14:56 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 181 expanded)
%              Number of clauses        :   32 (  60 expanded)
%              Number of leaves         :   10 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :  409 (1280 expanded)
%              Number of equality atoms :   36 ( 134 expanded)
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

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

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

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X12] :
      ( ~ l1_orders_2(X12)
      | ~ v1_lattice3(X12)
      | ~ v2_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

fof(c_0_12,negated_conjecture,
    ( v3_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & v1_lattice3(esk3_0)
    & v2_lattice3(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & k12_lattice3(esk3_0,esk4_0,k13_lattice3(esk3_0,esk4_0,esk5_0)) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
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

fof(c_0_14,plain,(
    ! [X13] :
      ( ~ l1_orders_2(X13)
      | ~ v2_lattice3(X13)
      | ~ v2_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_15,plain,(
    ! [X9,X10,X11] :
      ( v2_struct_0(X9)
      | ~ v3_orders_2(X9)
      | ~ l1_orders_2(X9)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | r3_orders_2(X9,X10,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

cnf(c_0_16,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( v1_lattice3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X32,X33,X34] :
      ( ~ v5_orders_2(X32)
      | ~ v1_lattice3(X32)
      | ~ l1_orders_2(X32)
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | ~ m1_subset_1(X34,u1_struct_0(X32))
      | k13_lattice3(X32,X33,X34) = k10_lattice3(X32,X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

cnf(c_0_20,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_23,plain,(
    ! [X6,X7,X8] :
      ( ( ~ r3_orders_2(X6,X7,X8)
        | r1_orders_2(X6,X7,X8)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ m1_subset_1(X8,u1_struct_0(X6)) )
      & ( ~ r1_orders_2(X6,X7,X8)
        | r3_orders_2(X6,X7,X8)
        | v2_struct_0(X6)
        | ~ v3_orders_2(X6)
        | ~ l1_orders_2(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ m1_subset_1(X8,u1_struct_0(X6)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_28,negated_conjecture,
    ( k12_lattice3(esk3_0,esk4_0,k13_lattice3(esk3_0,esk4_0,esk5_0)) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_32,plain,(
    ! [X29,X30,X31] :
      ( ~ v5_orders_2(X29)
      | ~ v2_lattice3(X29)
      | ~ l1_orders_2(X29)
      | ~ m1_subset_1(X30,u1_struct_0(X29))
      | ~ m1_subset_1(X31,u1_struct_0(X29))
      | k12_lattice3(X29,X30,X31) = k11_lattice3(X29,X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

cnf(c_0_33,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ r1_orders_2(X2,esk2_4(X2,X3,X4,X1),X1)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_34,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | r1_orders_2(X2,esk2_4(X2,X3,X4,X1),X3)
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_35,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( r3_orders_2(esk3_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_18]),c_0_26])]),c_0_27])).

fof(c_0_37,plain,(
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

cnf(c_0_38,negated_conjecture,
    ( k12_lattice3(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0)) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_17]),c_0_25]),c_0_31]),c_0_18])])).

cnf(c_0_39,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( v2_lattice3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,plain,
    ( k11_lattice3(X1,X2,X3) = X2
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_18]),c_0_26])]),c_0_27])).

cnf(c_0_43,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_44,plain,(
    ! [X14,X15,X16] :
      ( ~ l1_orders_2(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | m1_subset_1(k10_lattice3(X14,X15,X16),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).

cnf(c_0_45,negated_conjecture,
    ( k11_lattice3(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0)) != esk4_0
    | ~ m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_30]),c_0_40]),c_0_31]),c_0_18])])).

cnf(c_0_46,negated_conjecture,
    ( k11_lattice3(esk3_0,X1,X2) = X1
    | ~ r1_orders_2(esk3_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_30]),c_0_40]),c_0_18])])).

cnf(c_0_47,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_43,c_0_16])).

cnf(c_0_48,plain,
    ( m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_orders_2(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_31])])).

cnf(c_0_50,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( ~ m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_30]),c_0_17]),c_0_25]),c_0_31]),c_0_18])])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_48]),c_0_25]),c_0_31]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n012.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 13:24:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.030 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t18_lattice3, conjecture, ![X1]:(((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k12_lattice3(X1,X2,k13_lattice3(X1,X2,X3))=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_lattice3)).
% 0.19/0.37  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.19/0.37  fof(l28_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k11_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 0.19/0.37  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 0.19/0.37  fof(reflexivity_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_orders_2(X1,X2,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 0.19/0.37  fof(redefinition_k13_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 0.19/0.37  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.19/0.37  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.19/0.37  fof(l26_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k10_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 0.19/0.37  fof(dt_k10_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 0.19/0.37  fof(c_0_10, negated_conjecture, ~(![X1]:(((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k12_lattice3(X1,X2,k13_lattice3(X1,X2,X3))=X2)))), inference(assume_negation,[status(cth)],[t18_lattice3])).
% 0.19/0.37  fof(c_0_11, plain, ![X12]:(~l1_orders_2(X12)|(~v1_lattice3(X12)|~v2_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.19/0.37  fof(c_0_12, negated_conjecture, (((((v3_orders_2(esk3_0)&v5_orders_2(esk3_0))&v1_lattice3(esk3_0))&v2_lattice3(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&k12_lattice3(esk3_0,esk4_0,k13_lattice3(esk3_0,esk4_0,esk5_0))!=esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.19/0.37  fof(c_0_13, plain, ![X23, X24, X25, X26, X27]:((((r1_orders_2(X23,X26,X24)|X26!=k11_lattice3(X23,X24,X25)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v5_orders_2(X23)|~v2_lattice3(X23)|~l1_orders_2(X23)))&(r1_orders_2(X23,X26,X25)|X26!=k11_lattice3(X23,X24,X25)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v5_orders_2(X23)|~v2_lattice3(X23)|~l1_orders_2(X23))))&(~m1_subset_1(X27,u1_struct_0(X23))|(~r1_orders_2(X23,X27,X24)|~r1_orders_2(X23,X27,X25)|r1_orders_2(X23,X27,X26))|X26!=k11_lattice3(X23,X24,X25)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v5_orders_2(X23)|~v2_lattice3(X23)|~l1_orders_2(X23))))&((m1_subset_1(esk2_4(X23,X24,X25,X26),u1_struct_0(X23))|(~r1_orders_2(X23,X26,X24)|~r1_orders_2(X23,X26,X25))|X26=k11_lattice3(X23,X24,X25)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v5_orders_2(X23)|~v2_lattice3(X23)|~l1_orders_2(X23)))&(((r1_orders_2(X23,esk2_4(X23,X24,X25,X26),X24)|(~r1_orders_2(X23,X26,X24)|~r1_orders_2(X23,X26,X25))|X26=k11_lattice3(X23,X24,X25)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v5_orders_2(X23)|~v2_lattice3(X23)|~l1_orders_2(X23)))&(r1_orders_2(X23,esk2_4(X23,X24,X25,X26),X25)|(~r1_orders_2(X23,X26,X24)|~r1_orders_2(X23,X26,X25))|X26=k11_lattice3(X23,X24,X25)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v5_orders_2(X23)|~v2_lattice3(X23)|~l1_orders_2(X23))))&(~r1_orders_2(X23,esk2_4(X23,X24,X25,X26),X26)|(~r1_orders_2(X23,X26,X24)|~r1_orders_2(X23,X26,X25))|X26=k11_lattice3(X23,X24,X25)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v5_orders_2(X23)|~v2_lattice3(X23)|~l1_orders_2(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).
% 0.19/0.37  fof(c_0_14, plain, ![X13]:(~l1_orders_2(X13)|(~v2_lattice3(X13)|~v2_struct_0(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 0.19/0.37  fof(c_0_15, plain, ![X9, X10, X11]:(v2_struct_0(X9)|~v3_orders_2(X9)|~l1_orders_2(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))|r3_orders_2(X9,X10,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).
% 0.19/0.37  cnf(c_0_16, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (v1_lattice3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  fof(c_0_19, plain, ![X32, X33, X34]:(~v5_orders_2(X32)|~v1_lattice3(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,u1_struct_0(X32))|~m1_subset_1(X34,u1_struct_0(X32))|k13_lattice3(X32,X33,X34)=k10_lattice3(X32,X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).
% 0.19/0.37  cnf(c_0_20, plain, (X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,esk2_4(X1,X2,X3,X4),X4)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_21, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_22, plain, (r1_orders_2(X1,esk2_4(X1,X2,X3,X4),X2)|X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  fof(c_0_23, plain, ![X6, X7, X8]:((~r3_orders_2(X6,X7,X8)|r1_orders_2(X6,X7,X8)|(v2_struct_0(X6)|~v3_orders_2(X6)|~l1_orders_2(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))&(~r1_orders_2(X6,X7,X8)|r3_orders_2(X6,X7,X8)|(v2_struct_0(X6)|~v3_orders_2(X6)|~l1_orders_2(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.19/0.37  cnf(c_0_24, plain, (v2_struct_0(X1)|r3_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (k12_lattice3(esk3_0,esk4_0,k13_lattice3(esk3_0,esk4_0,esk5_0))!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_29, plain, (k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  fof(c_0_32, plain, ![X29, X30, X31]:(~v5_orders_2(X29)|~v2_lattice3(X29)|~l1_orders_2(X29)|~m1_subset_1(X30,u1_struct_0(X29))|~m1_subset_1(X31,u1_struct_0(X29))|k12_lattice3(X29,X30,X31)=k11_lattice3(X29,X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.19/0.37  cnf(c_0_33, plain, (X1=k11_lattice3(X2,X3,X4)|~v5_orders_2(X2)|~v2_lattice3(X2)|~r1_orders_2(X2,esk2_4(X2,X3,X4,X1),X1)|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.37  cnf(c_0_34, plain, (X1=k11_lattice3(X2,X3,X4)|r1_orders_2(X2,esk2_4(X2,X3,X4,X1),X3)|~v5_orders_2(X2)|~v2_lattice3(X2)|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_22, c_0_21])).
% 0.19/0.37  cnf(c_0_35, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (r3_orders_2(esk3_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_18]), c_0_26])]), c_0_27])).
% 0.19/0.37  fof(c_0_37, plain, ![X17, X18, X19, X20, X21]:((((r1_orders_2(X17,X18,X20)|X20!=k10_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v1_lattice3(X17)|~l1_orders_2(X17)))&(r1_orders_2(X17,X19,X20)|X20!=k10_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v1_lattice3(X17)|~l1_orders_2(X17))))&(~m1_subset_1(X21,u1_struct_0(X17))|(~r1_orders_2(X17,X18,X21)|~r1_orders_2(X17,X19,X21)|r1_orders_2(X17,X20,X21))|X20!=k10_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v1_lattice3(X17)|~l1_orders_2(X17))))&((m1_subset_1(esk1_4(X17,X18,X19,X20),u1_struct_0(X17))|(~r1_orders_2(X17,X18,X20)|~r1_orders_2(X17,X19,X20))|X20=k10_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v1_lattice3(X17)|~l1_orders_2(X17)))&(((r1_orders_2(X17,X18,esk1_4(X17,X18,X19,X20))|(~r1_orders_2(X17,X18,X20)|~r1_orders_2(X17,X19,X20))|X20=k10_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v1_lattice3(X17)|~l1_orders_2(X17)))&(r1_orders_2(X17,X19,esk1_4(X17,X18,X19,X20))|(~r1_orders_2(X17,X18,X20)|~r1_orders_2(X17,X19,X20))|X20=k10_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v1_lattice3(X17)|~l1_orders_2(X17))))&(~r1_orders_2(X17,X20,esk1_4(X17,X18,X19,X20))|(~r1_orders_2(X17,X18,X20)|~r1_orders_2(X17,X19,X20))|X20=k10_lattice3(X17,X18,X19)|~m1_subset_1(X20,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~v5_orders_2(X17)|~v1_lattice3(X17)|~l1_orders_2(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (k12_lattice3(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0))!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_17]), c_0_25]), c_0_31]), c_0_18])])).
% 0.19/0.37  cnf(c_0_39, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (v2_lattice3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_41, plain, (k11_lattice3(X1,X2,X3)=X2|~v5_orders_2(X1)|~v2_lattice3(X1)|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X2,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (r1_orders_2(esk3_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_18]), c_0_26])]), c_0_27])).
% 0.19/0.37  cnf(c_0_43, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X3!=k10_lattice3(X1,X2,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.37  fof(c_0_44, plain, ![X14, X15, X16]:(~l1_orders_2(X14)|~m1_subset_1(X15,u1_struct_0(X14))|~m1_subset_1(X16,u1_struct_0(X14))|m1_subset_1(k10_lattice3(X14,X15,X16),u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (k11_lattice3(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0))!=esk4_0|~m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_30]), c_0_40]), c_0_31]), c_0_18])])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, (k11_lattice3(esk3_0,X1,X2)=X1|~r1_orders_2(esk3_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_30]), c_0_40]), c_0_18])])).
% 0.19/0.37  cnf(c_0_47, plain, (r1_orders_2(X1,X2,X3)|X3!=k10_lattice3(X1,X2,X4)|~v5_orders_2(X1)|~v1_lattice3(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[c_0_43, c_0_16])).
% 0.19/0.37  cnf(c_0_48, plain, (m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.37  cnf(c_0_49, negated_conjecture, (~r1_orders_2(esk3_0,esk4_0,k10_lattice3(esk3_0,esk4_0,esk5_0))|~m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_31])])).
% 0.19/0.37  cnf(c_0_50, plain, (r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))|~v5_orders_2(X1)|~v1_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_47]), c_0_48])).
% 0.19/0.37  cnf(c_0_51, negated_conjecture, (~m1_subset_1(k10_lattice3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_30]), c_0_17]), c_0_25]), c_0_31]), c_0_18])])).
% 0.19/0.37  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_48]), c_0_25]), c_0_31]), c_0_18])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 53
% 0.19/0.37  # Proof object clause steps            : 32
% 0.19/0.37  # Proof object formula steps           : 21
% 0.19/0.37  # Proof object conjectures             : 20
% 0.19/0.37  # Proof object clause conjectures      : 17
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 18
% 0.19/0.37  # Proof object initial formulas used   : 10
% 0.19/0.37  # Proof object generating inferences   : 11
% 0.19/0.37  # Proof object simplifying inferences  : 41
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 10
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 30
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 30
% 0.19/0.37  # Processed clauses                    : 100
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 26
% 0.19/0.37  # ...remaining for further processing  : 74
% 0.19/0.37  # Other redundant clauses eliminated   : 12
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 151
% 0.19/0.37  # ...of the previous two non-trivial   : 119
% 0.19/0.37  # Contextual simplify-reflections      : 18
% 0.19/0.37  # Paramodulations                      : 133
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 18
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 74
% 0.19/0.37  #    Positive orientable unit clauses  : 7
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 5
% 0.19/0.37  #    Non-unit-clauses                  : 62
% 0.19/0.37  # Current number of unprocessed clauses: 47
% 0.19/0.37  # ...number of literals in the above   : 437
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 0
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 1404
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 213
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 42
% 0.19/0.37  # Unit Clause-clause subsumption calls : 16
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 0
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 8963
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.040 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.044 s
% 0.19/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
