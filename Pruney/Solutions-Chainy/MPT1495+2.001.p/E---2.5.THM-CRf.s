%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:58 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 481 expanded)
%              Number of clauses        :   58 ( 168 expanded)
%              Number of leaves         :   13 ( 127 expanded)
%              Depth                    :   20
%              Number of atoms          :  555 (3324 expanded)
%              Number of equality atoms :    6 (  39 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   28 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X2,X3)
      <=> r1_lattices(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(t7_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r3_lattices(X1,X2,X3)
              <=> r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_lattice3)).

fof(cc1_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v4_lattices(X1)
          & v5_lattices(X1)
          & v6_lattices(X1)
          & v7_lattices(X1)
          & v8_lattices(X1)
          & v9_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

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

fof(dt_k3_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ( v1_orders_2(k3_lattice3(X1))
        & v3_orders_2(k3_lattice3(X1))
        & v4_orders_2(k3_lattice3(X1))
        & v5_orders_2(k3_lattice3(X1))
        & l1_orders_2(k3_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_lattice3)).

fof(dt_k4_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattice3(X1,X2),u1_struct_0(k3_lattice3(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattice3)).

fof(fc4_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ( ~ v2_struct_0(k3_lattice3(X1))
        & v1_orders_2(k3_lattice3(X1))
        & v3_orders_2(k3_lattice3(X1))
        & v4_orders_2(k3_lattice3(X1))
        & v5_orders_2(k3_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_lattice3)).

fof(t28_lattice3,conjecture,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & l3_lattices(X2) )
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(X2))
         => ( r3_lattice3(X2,X3,X1)
          <=> r1_lattice3(k3_lattice3(X2),X1,k4_lattice3(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_lattice3)).

fof(d16_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r3_lattice3(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X4,X3)
                   => r1_lattices(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

fof(d3_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattice3(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattice3)).

fof(d8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(dt_k5_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
     => m1_subset_1(k5_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattice3)).

fof(d4_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
         => k5_lattice3(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_lattice3)).

fof(c_0_13,plain,(
    ! [X9,X10,X11] :
      ( ( ~ r3_lattices(X9,X10,X11)
        | r1_lattices(X9,X10,X11)
        | v2_struct_0(X9)
        | ~ v6_lattices(X9)
        | ~ v8_lattices(X9)
        | ~ v9_lattices(X9)
        | ~ l3_lattices(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9)) )
      & ( ~ r1_lattices(X9,X10,X11)
        | r3_lattices(X9,X10,X11)
        | v2_struct_0(X9)
        | ~ v6_lattices(X9)
        | ~ v8_lattices(X9)
        | ~ v9_lattices(X9)
        | ~ l3_lattices(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

fof(c_0_14,plain,(
    ! [X33,X34,X35] :
      ( ( ~ r3_lattices(X33,X34,X35)
        | r3_orders_2(k3_lattice3(X33),k4_lattice3(X33,X34),k4_lattice3(X33,X35))
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ l3_lattices(X33) )
      & ( ~ r3_orders_2(k3_lattice3(X33),k4_lattice3(X33,X34),k4_lattice3(X33,X35))
        | r3_lattices(X33,X34,X35)
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ l3_lattices(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_lattice3])])])])])).

fof(c_0_15,plain,(
    ! [X8] :
      ( ( ~ v2_struct_0(X8)
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ l3_lattices(X8) )
      & ( v4_lattices(X8)
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ l3_lattices(X8) )
      & ( v5_lattices(X8)
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ l3_lattices(X8) )
      & ( v6_lattices(X8)
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ l3_lattices(X8) )
      & ( v7_lattices(X8)
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ l3_lattices(X8) )
      & ( v8_lattices(X8)
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ l3_lattices(X8) )
      & ( v9_lattices(X8)
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ l3_lattices(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_16,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X5,X6,X7] :
      ( ( ~ r3_orders_2(X5,X6,X7)
        | r1_orders_2(X5,X6,X7)
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ l1_orders_2(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ m1_subset_1(X7,u1_struct_0(X5)) )
      & ( ~ r1_orders_2(X5,X6,X7)
        | r3_orders_2(X5,X6,X7)
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ l1_orders_2(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ m1_subset_1(X7,u1_struct_0(X5)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

fof(c_0_22,plain,(
    ! [X27] :
      ( ( v1_orders_2(k3_lattice3(X27))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ l3_lattices(X27) )
      & ( v3_orders_2(k3_lattice3(X27))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ l3_lattices(X27) )
      & ( v4_orders_2(k3_lattice3(X27))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ l3_lattices(X27) )
      & ( v5_orders_2(k3_lattice3(X27))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ l3_lattices(X27) )
      & ( l1_orders_2(k3_lattice3(X27))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ l3_lattices(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_lattice3])])])])).

fof(c_0_23,plain,(
    ! [X28,X29] :
      ( v2_struct_0(X28)
      | ~ v10_lattices(X28)
      | ~ l3_lattices(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | m1_subset_1(k4_lattice3(X28,X29),u1_struct_0(k3_lattice3(X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattice3])])])).

fof(c_0_24,plain,(
    ! [X32] :
      ( ( ~ v2_struct_0(k3_lattice3(X32))
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ l3_lattices(X32) )
      & ( v1_orders_2(k3_lattice3(X32))
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ l3_lattices(X32) )
      & ( v3_orders_2(k3_lattice3(X32))
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ l3_lattices(X32) )
      & ( v4_orders_2(k3_lattice3(X32))
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ l3_lattices(X32) )
      & ( v5_orders_2(k3_lattice3(X32))
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ l3_lattices(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_lattice3])])])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( ~ v2_struct_0(X2)
          & v10_lattices(X2)
          & l3_lattices(X2) )
       => ! [X3] :
            ( m1_subset_1(X3,u1_struct_0(X2))
           => ( r3_lattice3(X2,X3,X1)
            <=> r1_lattice3(k3_lattice3(X2),X1,k4_lattice3(X2,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_lattice3])).

fof(c_0_26,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r3_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r2_hidden(X15,X14)
        | r1_lattices(X12,X13,X15)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk1_3(X12,X13,X16),u1_struct_0(X12))
        | r3_lattice3(X12,X13,X16)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( r2_hidden(esk1_3(X12,X13,X16),X16)
        | r3_lattice3(X12,X13,X16)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( ~ r1_lattices(X12,X13,esk1_3(X12,X13,X16))
        | r3_lattice3(X12,X13,X16)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

cnf(c_0_27,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_28,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v3_orders_2(k3_lattice3(X1))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( l1_orders_2(k3_lattice3(X1))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattice3(X1,X2),u1_struct_0(k3_lattice3(X1)))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k3_lattice3(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v10_lattices(esk4_0)
    & l3_lattices(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & ( ~ r3_lattice3(esk4_0,esk5_0,esk3_0)
      | ~ r1_lattice3(k3_lattice3(esk4_0),esk3_0,k4_lattice3(esk4_0,esk5_0)) )
    & ( r3_lattice3(esk4_0,esk5_0,esk3_0)
      | r1_lattice3(k3_lattice3(esk4_0),esk3_0,k4_lattice3(esk4_0,esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])).

fof(c_0_34,plain,(
    ! [X18,X19] :
      ( v2_struct_0(X18)
      | ~ v10_lattices(X18)
      | ~ l3_lattices(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | k4_lattice3(X18,X19) = X19 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattice3])])])])).

cnf(c_0_35,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r1_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_31]),c_0_32])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_38,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r2_hidden(X25,X23)
        | r1_orders_2(X22,X24,X25)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk2_3(X22,X23,X24),u1_struct_0(X22))
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X23)
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( ~ r1_orders_2(X22,X24,esk2_3(X22,X23,X24))
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

cnf(c_0_39,negated_conjecture,
    ( r3_lattice3(esk4_0,esk5_0,esk3_0)
    | r1_lattice3(k3_lattice3(esk4_0),esk3_0,k4_lattice3(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | k4_lattice3(X1,X2) = X2
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( v10_lattices(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( l3_lattices(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r1_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,esk1_3(X1,X2,X3)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_46,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( r1_lattice3(k3_lattice3(esk4_0),esk3_0,esk5_0)
    | r3_lattice3(esk4_0,esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_43])]),c_0_44])).

cnf(c_0_48,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r1_orders_2(k3_lattice3(X1),X2,k4_lattice3(X1,esk1_3(X1,X2,X3)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r3_lattice3(esk4_0,esk5_0,esk3_0)
    | r1_orders_2(k3_lattice3(esk4_0),esk5_0,X1)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(esk4_0)))
    | ~ l1_orders_2(k3_lattice3(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_51,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r1_orders_2(k3_lattice3(X1),X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_40]),c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( r3_lattice3(esk4_0,esk5_0,esk3_0)
    | r3_lattice3(X1,X2,esk3_0)
    | r1_orders_2(k3_lattice3(esk4_0),esk5_0,esk1_3(X1,X2,esk3_0))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(esk1_3(X1,X2,esk3_0),u1_struct_0(k3_lattice3(esk4_0)))
    | ~ m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(k3_lattice3(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( r3_lattice3(esk4_0,esk5_0,esk3_0)
    | ~ m1_subset_1(esk1_3(esk4_0,esk5_0,esk3_0),u1_struct_0(k3_lattice3(esk4_0)))
    | ~ m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))
    | ~ l1_orders_2(k3_lattice3(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_41]),c_0_42]),c_0_43])]),c_0_44])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,u1_struct_0(k3_lattice3(X2)))
    | v2_struct_0(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_40])).

cnf(c_0_55,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_56,negated_conjecture,
    ( r3_lattice3(esk4_0,esk5_0,esk3_0)
    | ~ m1_subset_1(esk1_3(esk4_0,esk5_0,esk3_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))
    | ~ l1_orders_2(k3_lattice3(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_41]),c_0_42])]),c_0_44])).

cnf(c_0_57,plain,
    ( r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_58,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_20]),c_0_18]),c_0_19])).

cnf(c_0_59,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_60,negated_conjecture,
    ( r3_lattice3(esk4_0,esk5_0,esk3_0)
    | ~ m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))
    | ~ l1_orders_2(k3_lattice3(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_37]),c_0_42]),c_0_43])]),c_0_44])).

cnf(c_0_61,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_62,plain,
    ( r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( r1_lattices(esk4_0,esk5_0,X1)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ l1_orders_2(k3_lattice3(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_42]),c_0_43])]),c_0_44])).

cnf(c_0_64,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_65,plain,
    ( r1_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_29]),c_0_30]),c_0_31]),c_0_31]),c_0_32])).

cnf(c_0_66,negated_conjecture,
    ( r1_lattice3(X1,esk3_0,X2)
    | r1_lattices(esk4_0,esk5_0,esk2_3(X1,esk3_0,X2))
    | ~ m1_subset_1(esk2_3(X1,esk3_0,X2),u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(k3_lattice3(esk4_0))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( r1_lattice3(X1,esk3_0,X2)
    | r1_orders_2(k3_lattice3(esk4_0),k4_lattice3(esk4_0,esk5_0),k4_lattice3(esk4_0,esk2_3(X1,esk3_0,X2)))
    | ~ m1_subset_1(esk2_3(X1,esk3_0,X2),u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(k3_lattice3(esk4_0))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_41]),c_0_42]),c_0_43])]),c_0_44])).

fof(c_0_68,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ v10_lattices(X30)
      | ~ l3_lattices(X30)
      | ~ m1_subset_1(X31,u1_struct_0(k3_lattice3(X30)))
      | m1_subset_1(k5_lattice3(X30,X31),u1_struct_0(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattice3])])])).

fof(c_0_69,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ v10_lattices(X20)
      | ~ l3_lattices(X20)
      | ~ m1_subset_1(X21,u1_struct_0(k3_lattice3(X20)))
      | k5_lattice3(X20,X21) = X21 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_lattice3])])])])).

cnf(c_0_70,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk2_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_71,negated_conjecture,
    ( r1_lattice3(X1,esk3_0,X2)
    | r1_orders_2(k3_lattice3(esk4_0),k4_lattice3(esk4_0,esk5_0),esk2_3(X1,esk3_0,X2))
    | ~ m1_subset_1(esk2_3(X1,esk3_0,X2),u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(k3_lattice3(esk4_0))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_40]),c_0_41]),c_0_42])]),c_0_44])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattice3(X1,X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | k5_lattice3(X1,X2) = X2
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( r1_lattice3(k3_lattice3(esk4_0),esk3_0,k4_lattice3(esk4_0,esk5_0))
    | ~ m1_subset_1(esk2_3(k3_lattice3(esk4_0),esk3_0,k4_lattice3(esk4_0,esk5_0)),u1_struct_0(esk4_0))
    | ~ m1_subset_1(k4_lattice3(esk4_0,esk5_0),u1_struct_0(k3_lattice3(esk4_0)))
    | ~ m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))
    | ~ l1_orders_2(k3_lattice3(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X2))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_76,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_77,negated_conjecture,
    ( ~ r3_lattice3(esk4_0,esk5_0,esk3_0)
    | ~ r1_lattice3(k3_lattice3(esk4_0),esk3_0,k4_lattice3(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_78,negated_conjecture,
    ( r1_lattice3(k3_lattice3(esk4_0),esk3_0,esk5_0)
    | ~ m1_subset_1(esk2_3(k3_lattice3(esk4_0),esk3_0,esk5_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))
    | ~ l1_orders_2(k3_lattice3(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_40]),c_0_41]),c_0_42]),c_0_43])]),c_0_44])).

cnf(c_0_79,plain,
    ( r1_lattice3(k3_lattice3(X1),X2,X3)
    | m1_subset_1(esk2_3(k3_lattice3(X1),X2,X3),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k3_lattice3(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_30])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_lattice3(k3_lattice3(esk4_0),esk3_0,esk5_0)
    | ~ r3_lattice3(esk4_0,esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_40]),c_0_41]),c_0_42]),c_0_43])]),c_0_44])).

cnf(c_0_81,negated_conjecture,
    ( r1_lattice3(k3_lattice3(esk4_0),esk3_0,esk5_0)
    | ~ m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))
    | ~ l1_orders_2(k3_lattice3(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_41]),c_0_42])]),c_0_44])).

cnf(c_0_82,negated_conjecture,
    ( ~ m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))
    | ~ l1_orders_2(k3_lattice3(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_60])).

cnf(c_0_83,negated_conjecture,
    ( ~ l1_orders_2(k3_lattice3(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_54]),c_0_41]),c_0_42]),c_0_43])]),c_0_44])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_30]),c_0_41]),c_0_42])]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.20/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.030 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.20/0.41  fof(t7_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_lattices(X1,X2,X3)<=>r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_lattice3)).
% 0.20/0.41  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.20/0.41  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.20/0.41  fof(dt_k3_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>((((v1_orders_2(k3_lattice3(X1))&v3_orders_2(k3_lattice3(X1)))&v4_orders_2(k3_lattice3(X1)))&v5_orders_2(k3_lattice3(X1)))&l1_orders_2(k3_lattice3(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_lattice3)).
% 0.20/0.41  fof(dt_k4_lattice3, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k4_lattice3(X1,X2),u1_struct_0(k3_lattice3(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_lattice3)).
% 0.20/0.41  fof(fc4_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>((((~(v2_struct_0(k3_lattice3(X1)))&v1_orders_2(k3_lattice3(X1)))&v3_orders_2(k3_lattice3(X1)))&v4_orders_2(k3_lattice3(X1)))&v5_orders_2(k3_lattice3(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_lattice3)).
% 0.20/0.41  fof(t28_lattice3, conjecture, ![X1, X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>(r3_lattice3(X2,X3,X1)<=>r1_lattice3(k3_lattice3(X2),X1,k4_lattice3(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_lattice3)).
% 0.20/0.41  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 0.20/0.41  fof(d3_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattice3(X1,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattice3)).
% 0.20/0.41  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 0.20/0.41  fof(dt_k5_lattice3, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))))=>m1_subset_1(k5_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattice3)).
% 0.20/0.41  fof(d4_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))=>k5_lattice3(X1,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_lattice3)).
% 0.20/0.41  fof(c_0_13, plain, ![X9, X10, X11]:((~r3_lattices(X9,X10,X11)|r1_lattices(X9,X10,X11)|(v2_struct_0(X9)|~v6_lattices(X9)|~v8_lattices(X9)|~v9_lattices(X9)|~l3_lattices(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))&(~r1_lattices(X9,X10,X11)|r3_lattices(X9,X10,X11)|(v2_struct_0(X9)|~v6_lattices(X9)|~v8_lattices(X9)|~v9_lattices(X9)|~l3_lattices(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.20/0.41  fof(c_0_14, plain, ![X33, X34, X35]:((~r3_lattices(X33,X34,X35)|r3_orders_2(k3_lattice3(X33),k4_lattice3(X33,X34),k4_lattice3(X33,X35))|~m1_subset_1(X35,u1_struct_0(X33))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v10_lattices(X33)|~l3_lattices(X33)))&(~r3_orders_2(k3_lattice3(X33),k4_lattice3(X33,X34),k4_lattice3(X33,X35))|r3_lattices(X33,X34,X35)|~m1_subset_1(X35,u1_struct_0(X33))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v10_lattices(X33)|~l3_lattices(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_lattice3])])])])])).
% 0.20/0.41  fof(c_0_15, plain, ![X8]:(((((((~v2_struct_0(X8)|(v2_struct_0(X8)|~v10_lattices(X8))|~l3_lattices(X8))&(v4_lattices(X8)|(v2_struct_0(X8)|~v10_lattices(X8))|~l3_lattices(X8)))&(v5_lattices(X8)|(v2_struct_0(X8)|~v10_lattices(X8))|~l3_lattices(X8)))&(v6_lattices(X8)|(v2_struct_0(X8)|~v10_lattices(X8))|~l3_lattices(X8)))&(v7_lattices(X8)|(v2_struct_0(X8)|~v10_lattices(X8))|~l3_lattices(X8)))&(v8_lattices(X8)|(v2_struct_0(X8)|~v10_lattices(X8))|~l3_lattices(X8)))&(v9_lattices(X8)|(v2_struct_0(X8)|~v10_lattices(X8))|~l3_lattices(X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.20/0.41  cnf(c_0_16, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_17, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_18, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_19, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_20, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  fof(c_0_21, plain, ![X5, X6, X7]:((~r3_orders_2(X5,X6,X7)|r1_orders_2(X5,X6,X7)|(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))))&(~r1_orders_2(X5,X6,X7)|r3_orders_2(X5,X6,X7)|(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.20/0.41  fof(c_0_22, plain, ![X27]:(((((v1_orders_2(k3_lattice3(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~l3_lattices(X27)))&(v3_orders_2(k3_lattice3(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~l3_lattices(X27))))&(v4_orders_2(k3_lattice3(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~l3_lattices(X27))))&(v5_orders_2(k3_lattice3(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~l3_lattices(X27))))&(l1_orders_2(k3_lattice3(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~l3_lattices(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_lattice3])])])])).
% 0.20/0.41  fof(c_0_23, plain, ![X28, X29]:(v2_struct_0(X28)|~v10_lattices(X28)|~l3_lattices(X28)|~m1_subset_1(X29,u1_struct_0(X28))|m1_subset_1(k4_lattice3(X28,X29),u1_struct_0(k3_lattice3(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattice3])])])).
% 0.20/0.41  fof(c_0_24, plain, ![X32]:(((((~v2_struct_0(k3_lattice3(X32))|(v2_struct_0(X32)|~v10_lattices(X32)|~l3_lattices(X32)))&(v1_orders_2(k3_lattice3(X32))|(v2_struct_0(X32)|~v10_lattices(X32)|~l3_lattices(X32))))&(v3_orders_2(k3_lattice3(X32))|(v2_struct_0(X32)|~v10_lattices(X32)|~l3_lattices(X32))))&(v4_orders_2(k3_lattice3(X32))|(v2_struct_0(X32)|~v10_lattices(X32)|~l3_lattices(X32))))&(v5_orders_2(k3_lattice3(X32))|(v2_struct_0(X32)|~v10_lattices(X32)|~l3_lattices(X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_lattice3])])])])).
% 0.20/0.41  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>(r3_lattice3(X2,X3,X1)<=>r1_lattice3(k3_lattice3(X2),X1,k4_lattice3(X2,X3)))))), inference(assume_negation,[status(cth)],[t28_lattice3])).
% 0.20/0.41  fof(c_0_26, plain, ![X12, X13, X14, X15, X16]:((~r3_lattice3(X12,X13,X14)|(~m1_subset_1(X15,u1_struct_0(X12))|(~r2_hidden(X15,X14)|r1_lattices(X12,X13,X15)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~l3_lattices(X12)))&((m1_subset_1(esk1_3(X12,X13,X16),u1_struct_0(X12))|r3_lattice3(X12,X13,X16)|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~l3_lattices(X12)))&((r2_hidden(esk1_3(X12,X13,X16),X16)|r3_lattice3(X12,X13,X16)|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~l3_lattices(X12)))&(~r1_lattices(X12,X13,esk1_3(X12,X13,X16))|r3_lattice3(X12,X13,X16)|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~l3_lattices(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.20/0.41  cnf(c_0_27, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.20/0.41  cnf(c_0_28, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.41  cnf(c_0_29, plain, (v3_orders_2(k3_lattice3(X1))|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_30, plain, (l1_orders_2(k3_lattice3(X1))|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_31, plain, (v2_struct_0(X1)|m1_subset_1(k4_lattice3(X1,X2),u1_struct_0(k3_lattice3(X1)))|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_32, plain, (v2_struct_0(X1)|~v2_struct_0(k3_lattice3(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.41  fof(c_0_33, negated_conjecture, (((~v2_struct_0(esk4_0)&v10_lattices(esk4_0))&l3_lattices(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&((~r3_lattice3(esk4_0,esk5_0,esk3_0)|~r1_lattice3(k3_lattice3(esk4_0),esk3_0,k4_lattice3(esk4_0,esk5_0)))&(r3_lattice3(esk4_0,esk5_0,esk3_0)|r1_lattice3(k3_lattice3(esk4_0),esk3_0,k4_lattice3(esk4_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])).
% 0.20/0.41  fof(c_0_34, plain, ![X18, X19]:(v2_struct_0(X18)|~v10_lattices(X18)|~l3_lattices(X18)|(~m1_subset_1(X19,u1_struct_0(X18))|k4_lattice3(X18,X19)=X19)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattice3])])])])).
% 0.20/0.41  cnf(c_0_35, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk1_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_36, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~r1_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_31]), c_0_32])).
% 0.20/0.41  cnf(c_0_37, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  fof(c_0_38, plain, ![X22, X23, X24, X25]:((~r1_lattice3(X22,X23,X24)|(~m1_subset_1(X25,u1_struct_0(X22))|(~r2_hidden(X25,X23)|r1_orders_2(X22,X24,X25)))|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&((m1_subset_1(esk2_3(X22,X23,X24),u1_struct_0(X22))|r1_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&((r2_hidden(esk2_3(X22,X23,X24),X23)|r1_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&(~r1_orders_2(X22,X24,esk2_3(X22,X23,X24))|r1_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (r3_lattice3(esk4_0,esk5_0,esk3_0)|r1_lattice3(k3_lattice3(esk4_0),esk3_0,k4_lattice3(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_40, plain, (v2_struct_0(X1)|k4_lattice3(X1,X2)=X2|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (v10_lattices(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_42, negated_conjecture, (l3_lattices(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_45, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~r1_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,esk1_3(X1,X2,X3)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.20/0.41  cnf(c_0_46, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (r1_lattice3(k3_lattice3(esk4_0),esk3_0,esk5_0)|r3_lattice3(esk4_0,esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42]), c_0_43])]), c_0_44])).
% 0.20/0.41  cnf(c_0_48, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~r1_orders_2(k3_lattice3(X1),X2,k4_lattice3(X1,esk1_3(X1,X2,X3)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_45, c_0_40])).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (r3_lattice3(esk4_0,esk5_0,esk3_0)|r1_orders_2(k3_lattice3(esk4_0),esk5_0,X1)|~r2_hidden(X1,esk3_0)|~m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))|~m1_subset_1(X1,u1_struct_0(k3_lattice3(esk4_0)))|~l1_orders_2(k3_lattice3(esk4_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.41  cnf(c_0_50, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_51, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~r1_orders_2(k3_lattice3(X1),X2,esk1_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_40]), c_0_37])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (r3_lattice3(esk4_0,esk5_0,esk3_0)|r3_lattice3(X1,X2,esk3_0)|r1_orders_2(k3_lattice3(esk4_0),esk5_0,esk1_3(X1,X2,esk3_0))|v2_struct_0(X1)|~l3_lattices(X1)|~m1_subset_1(esk1_3(X1,X2,esk3_0),u1_struct_0(k3_lattice3(esk4_0)))|~m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(k3_lattice3(esk4_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (r3_lattice3(esk4_0,esk5_0,esk3_0)|~m1_subset_1(esk1_3(esk4_0,esk5_0,esk3_0),u1_struct_0(k3_lattice3(esk4_0)))|~m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))|~l1_orders_2(k3_lattice3(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_41]), c_0_42]), c_0_43])]), c_0_44])).
% 0.20/0.41  cnf(c_0_54, plain, (m1_subset_1(X1,u1_struct_0(k3_lattice3(X2)))|v2_struct_0(X2)|~v10_lattices(X2)|~l3_lattices(X2)|~m1_subset_1(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_31, c_0_40])).
% 0.20/0.41  cnf(c_0_55, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, (r3_lattice3(esk4_0,esk5_0,esk3_0)|~m1_subset_1(esk1_3(esk4_0,esk5_0,esk3_0),u1_struct_0(esk4_0))|~m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))|~l1_orders_2(k3_lattice3(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_41]), c_0_42])]), c_0_44])).
% 0.20/0.41  cnf(c_0_57, plain, (r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_58, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_20]), c_0_18]), c_0_19])).
% 0.20/0.41  cnf(c_0_59, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (r3_lattice3(esk4_0,esk5_0,esk3_0)|~m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))|~l1_orders_2(k3_lattice3(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_37]), c_0_42]), c_0_43])]), c_0_44])).
% 0.20/0.41  cnf(c_0_61, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.41  cnf(c_0_62, plain, (r3_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.41  cnf(c_0_63, negated_conjecture, (r1_lattices(esk4_0,esk5_0,X1)|~r2_hidden(X1,esk3_0)|~m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))|~m1_subset_1(X1,u1_struct_0(esk4_0))|~l1_orders_2(k3_lattice3(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_42]), c_0_43])]), c_0_44])).
% 0.20/0.41  cnf(c_0_64, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.41  cnf(c_0_65, plain, (r1_orders_2(k3_lattice3(X1),k4_lattice3(X1,X2),k4_lattice3(X1,X3))|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_29]), c_0_30]), c_0_31]), c_0_31]), c_0_32])).
% 0.20/0.41  cnf(c_0_66, negated_conjecture, (r1_lattice3(X1,esk3_0,X2)|r1_lattices(esk4_0,esk5_0,esk2_3(X1,esk3_0,X2))|~m1_subset_1(esk2_3(X1,esk3_0,X2),u1_struct_0(esk4_0))|~m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(k3_lattice3(esk4_0))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.41  cnf(c_0_67, negated_conjecture, (r1_lattice3(X1,esk3_0,X2)|r1_orders_2(k3_lattice3(esk4_0),k4_lattice3(esk4_0,esk5_0),k4_lattice3(esk4_0,esk2_3(X1,esk3_0,X2)))|~m1_subset_1(esk2_3(X1,esk3_0,X2),u1_struct_0(esk4_0))|~m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(k3_lattice3(esk4_0))|~l1_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_41]), c_0_42]), c_0_43])]), c_0_44])).
% 0.20/0.41  fof(c_0_68, plain, ![X30, X31]:(v2_struct_0(X30)|~v10_lattices(X30)|~l3_lattices(X30)|~m1_subset_1(X31,u1_struct_0(k3_lattice3(X30)))|m1_subset_1(k5_lattice3(X30,X31),u1_struct_0(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattice3])])])).
% 0.20/0.41  fof(c_0_69, plain, ![X20, X21]:(v2_struct_0(X20)|~v10_lattices(X20)|~l3_lattices(X20)|(~m1_subset_1(X21,u1_struct_0(k3_lattice3(X20)))|k5_lattice3(X20,X21)=X21)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_lattice3])])])])).
% 0.20/0.41  cnf(c_0_70, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk2_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.41  cnf(c_0_71, negated_conjecture, (r1_lattice3(X1,esk3_0,X2)|r1_orders_2(k3_lattice3(esk4_0),k4_lattice3(esk4_0,esk5_0),esk2_3(X1,esk3_0,X2))|~m1_subset_1(esk2_3(X1,esk3_0,X2),u1_struct_0(esk4_0))|~m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(k3_lattice3(esk4_0))|~l1_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_40]), c_0_41]), c_0_42])]), c_0_44])).
% 0.20/0.41  cnf(c_0_72, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattice3(X1,X2),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.41  cnf(c_0_73, plain, (v2_struct_0(X1)|k5_lattice3(X1,X2)=X2|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.41  cnf(c_0_74, negated_conjecture, (r1_lattice3(k3_lattice3(esk4_0),esk3_0,k4_lattice3(esk4_0,esk5_0))|~m1_subset_1(esk2_3(k3_lattice3(esk4_0),esk3_0,k4_lattice3(esk4_0,esk5_0)),u1_struct_0(esk4_0))|~m1_subset_1(k4_lattice3(esk4_0,esk5_0),u1_struct_0(k3_lattice3(esk4_0)))|~m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))|~l1_orders_2(k3_lattice3(esk4_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.41  cnf(c_0_75, plain, (m1_subset_1(X1,u1_struct_0(X2))|v2_struct_0(X2)|~v10_lattices(X2)|~l3_lattices(X2)|~m1_subset_1(X1,u1_struct_0(k3_lattice3(X2)))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.20/0.41  cnf(c_0_76, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.41  cnf(c_0_77, negated_conjecture, (~r3_lattice3(esk4_0,esk5_0,esk3_0)|~r1_lattice3(k3_lattice3(esk4_0),esk3_0,k4_lattice3(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_78, negated_conjecture, (r1_lattice3(k3_lattice3(esk4_0),esk3_0,esk5_0)|~m1_subset_1(esk2_3(k3_lattice3(esk4_0),esk3_0,esk5_0),u1_struct_0(esk4_0))|~m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))|~l1_orders_2(k3_lattice3(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_40]), c_0_41]), c_0_42]), c_0_43])]), c_0_44])).
% 0.20/0.41  cnf(c_0_79, plain, (r1_lattice3(k3_lattice3(X1),X2,X3)|m1_subset_1(esk2_3(k3_lattice3(X1),X2,X3),u1_struct_0(X1))|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X3,u1_struct_0(k3_lattice3(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_30])).
% 0.20/0.41  cnf(c_0_80, negated_conjecture, (~r1_lattice3(k3_lattice3(esk4_0),esk3_0,esk5_0)|~r3_lattice3(esk4_0,esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_40]), c_0_41]), c_0_42]), c_0_43])]), c_0_44])).
% 0.20/0.41  cnf(c_0_81, negated_conjecture, (r1_lattice3(k3_lattice3(esk4_0),esk3_0,esk5_0)|~m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))|~l1_orders_2(k3_lattice3(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_41]), c_0_42])]), c_0_44])).
% 0.20/0.41  cnf(c_0_82, negated_conjecture, (~m1_subset_1(esk5_0,u1_struct_0(k3_lattice3(esk4_0)))|~l1_orders_2(k3_lattice3(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_60])).
% 0.20/0.41  cnf(c_0_83, negated_conjecture, (~l1_orders_2(k3_lattice3(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_54]), c_0_41]), c_0_42]), c_0_43])]), c_0_44])).
% 0.20/0.41  cnf(c_0_84, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_30]), c_0_41]), c_0_42])]), c_0_44]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 85
% 0.20/0.41  # Proof object clause steps            : 58
% 0.20/0.41  # Proof object formula steps           : 27
% 0.20/0.41  # Proof object conjectures             : 26
% 0.20/0.41  # Proof object clause conjectures      : 23
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 30
% 0.20/0.41  # Proof object initial formulas used   : 13
% 0.20/0.41  # Proof object generating inferences   : 28
% 0.20/0.41  # Proof object simplifying inferences  : 73
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 13
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 41
% 0.20/0.41  # Removed in clause preprocessing      : 1
% 0.20/0.41  # Initial clauses in saturation        : 40
% 0.20/0.41  # Processed clauses                    : 233
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 66
% 0.20/0.41  # ...remaining for further processing  : 167
% 0.20/0.41  # Other redundant clauses eliminated   : 0
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 33
% 0.20/0.41  # Backward-rewritten                   : 0
% 0.20/0.41  # Generated clauses                    : 322
% 0.20/0.41  # ...of the previous two non-trivial   : 303
% 0.20/0.41  # Contextual simplify-reflections      : 62
% 0.20/0.41  # Paramodulations                      : 322
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 0
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 98
% 0.20/0.41  #    Positive orientable unit clauses  : 3
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 2
% 0.20/0.41  #    Non-unit-clauses                  : 93
% 0.20/0.41  # Current number of unprocessed clauses: 146
% 0.20/0.41  # ...number of literals in the above   : 2010
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 69
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 14016
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1003
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 161
% 0.20/0.41  # Unit Clause-clause subsumption calls : 6
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 0
% 0.20/0.41  # BW rewrite match successes           : 0
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 22689
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.064 s
% 0.20/0.41  # System time              : 0.004 s
% 0.20/0.41  # Total time               : 0.068 s
% 0.20/0.41  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
