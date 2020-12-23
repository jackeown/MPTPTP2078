%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1509+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:19 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 530 expanded)
%              Number of clauses        :   55 ( 181 expanded)
%              Number of leaves         :   13 ( 129 expanded)
%              Depth                    :   11
%              Number of atoms          :  393 (3238 expanded)
%              Number of equality atoms :   45 ( 660 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
            & k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattice3)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

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

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(d17_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r4_lattice3(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X4,X3)
                   => r1_lattices(X1,X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

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

fof(dt_l2_lattices,axiom,(
    ! [X1] :
      ( l2_lattices(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l2_lattices)).

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

fof(reflexivity_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_lattices(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(t41_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( r2_hidden(X2,X3)
                & r4_lattice3(X1,X2,X3) )
             => k15_lattice3(X1,X3) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattice3)).

fof(t42_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( r2_hidden(X2,X3)
                & r3_lattice3(X1,X2,X3) )
             => k16_lattice3(X1,X3) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
              & k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t43_lattice3])).

fof(c_0_14,plain,(
    ! [X28,X29] :
      ( v1_xboole_0(X28)
      | ~ m1_subset_1(X29,X28)
      | k6_domain_1(X28,X29) = k1_tarski(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v10_lattices(esk4_0)
    & v4_lattice3(esk4_0)
    & l3_lattices(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & ( k15_lattice3(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) != esk5_0
      | k16_lattice3(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) != esk5_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X20,X19)
        | X20 = X18
        | X19 != k1_tarski(X18) )
      & ( X21 != X18
        | r2_hidden(X21,X19)
        | X19 != k1_tarski(X18) )
      & ( ~ r2_hidden(esk3_2(X22,X23),X23)
        | esk3_2(X22,X23) != X22
        | X23 = k1_tarski(X22) )
      & ( r2_hidden(esk3_2(X22,X23),X23)
        | esk3_2(X22,X23) = X22
        | X23 = k1_tarski(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_17,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r3_lattice3(X6,X7,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | ~ r2_hidden(X9,X8)
        | r1_lattices(X6,X7,X9)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) )
      & ( m1_subset_1(esk1_3(X6,X7,X10),u1_struct_0(X6))
        | r3_lattice3(X6,X7,X10)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) )
      & ( r2_hidden(esk1_3(X6,X7,X10),X10)
        | r3_lattice3(X6,X7,X10)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) )
      & ( ~ r1_lattices(X6,X7,esk1_3(X6,X7,X10))
        | r3_lattice3(X6,X7,X10)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

fof(c_0_18,plain,(
    ! [X27] :
      ( v2_struct_0(X27)
      | ~ l1_struct_0(X27)
      | ~ v1_xboole_0(u1_struct_0(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r4_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r2_hidden(X15,X14)
        | r1_lattices(X12,X15,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk2_3(X12,X13,X16),u1_struct_0(X12))
        | r4_lattice3(X12,X13,X16)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( r2_hidden(esk2_3(X12,X13,X16),X16)
        | r4_lattice3(X12,X13,X16)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( ~ r1_lattices(X12,esk2_3(X12,X13,X16),X13)
        | r4_lattice3(X12,X13,X16)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

cnf(c_0_22,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( l3_lattices(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk5_0) = k1_tarski(esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,esk5_0,X1),X1)
    | r3_lattice3(esk4_0,esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_20]),c_0_24])]),c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_33,plain,(
    ! [X5] :
      ( ( ~ v2_struct_0(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v4_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v5_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v6_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v7_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v8_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v9_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_34,negated_conjecture,
    ( k15_lattice3(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) != esk5_0
    | k16_lattice3(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk5_0) = k1_tarski(esk5_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_25])).

fof(c_0_36,plain,(
    ! [X25] :
      ( ~ l2_lattices(X25)
      | l1_struct_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l2_lattices])])).

cnf(c_0_37,negated_conjecture,
    ( r1_lattices(esk4_0,esk5_0,X1)
    | ~ r4_lattice3(esk4_0,X1,X2)
    | ~ r2_hidden(esk5_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_20]),c_0_24])]),c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( r3_lattice3(esk4_0,esk5_0,X1)
    | m1_subset_1(esk1_3(esk4_0,esk5_0,X1),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_20]),c_0_24])]),c_0_25])).

cnf(c_0_39,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( esk1_3(esk4_0,esk5_0,k1_tarski(X1)) = X1
    | r3_lattice3(esk4_0,esk5_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r4_lattice3(esk4_0,esk5_0,X1)
    | r2_hidden(esk2_3(esk4_0,esk5_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_20]),c_0_24])]),c_0_25])).

fof(c_0_42,plain,(
    ! [X30,X31,X32] :
      ( ( ~ r3_lattices(X30,X31,X32)
        | r1_lattices(X30,X31,X32)
        | v2_struct_0(X30)
        | ~ v6_lattices(X30)
        | ~ v8_lattices(X30)
        | ~ v9_lattices(X30)
        | ~ l3_lattices(X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(X30)) )
      & ( ~ r1_lattices(X30,X31,X32)
        | r3_lattices(X30,X31,X32)
        | v2_struct_0(X30)
        | ~ v6_lattices(X30)
        | ~ v8_lattices(X30)
        | ~ v9_lattices(X30)
        | ~ l3_lattices(X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_43,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( v10_lattices(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_47,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ v6_lattices(X33)
      | ~ v8_lattices(X33)
      | ~ v9_lattices(X33)
      | ~ l3_lattices(X33)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | ~ m1_subset_1(X35,u1_struct_0(X33))
      | r3_lattices(X33,X34,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_lattices])])])).

cnf(c_0_48,negated_conjecture,
    ( k15_lattice3(esk4_0,k1_tarski(esk5_0)) != esk5_0
    | k16_lattice3(esk4_0,k1_tarski(esk5_0)) != esk5_0
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_49,plain,
    ( l1_struct_0(X1)
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_50,plain,(
    ! [X26] :
      ( ( l1_lattices(X26)
        | ~ l3_lattices(X26) )
      & ( l2_lattices(X26)
        | ~ l3_lattices(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_51,plain,(
    ! [X36,X37,X38] :
      ( v2_struct_0(X36)
      | ~ v10_lattices(X36)
      | ~ v4_lattice3(X36)
      | ~ l3_lattices(X36)
      | ~ m1_subset_1(X37,u1_struct_0(X36))
      | ~ r2_hidden(X37,X38)
      | ~ r4_lattice3(X36,X37,X38)
      | k15_lattice3(X36,X38) = X37 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_lattice3])])])])).

cnf(c_0_52,negated_conjecture,
    ( r1_lattices(esk4_0,esk5_0,esk1_3(esk4_0,esk5_0,X1))
    | r3_lattice3(esk4_0,esk5_0,X1)
    | ~ r4_lattice3(esk4_0,esk1_3(esk4_0,esk5_0,X1),X2)
    | ~ r2_hidden(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( r3_lattice3(esk4_0,esk5_0,k1_tarski(X1))
    | ~ r1_lattices(esk4_0,esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_20]),c_0_24])]),c_0_25])).

cnf(c_0_54,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk2_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( esk2_3(esk4_0,esk5_0,k1_tarski(X1)) = X1
    | r4_lattice3(esk4_0,esk5_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_41])).

cnf(c_0_56,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,negated_conjecture,
    ( v9_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_24])]),c_0_25])).

cnf(c_0_58,negated_conjecture,
    ( v8_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_44]),c_0_24])]),c_0_25])).

cnf(c_0_59,negated_conjecture,
    ( v6_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_44]),c_0_24])]),c_0_25])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,X2,X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( k15_lattice3(esk4_0,k1_tarski(esk5_0)) != esk5_0
    | k16_lattice3(esk4_0,k1_tarski(esk5_0)) != esk5_0
    | ~ l2_lattices(esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_62,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X3) = X2
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X3)
    | ~ r4_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( v4_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_66,plain,(
    ! [X39,X40,X41] :
      ( v2_struct_0(X39)
      | ~ v10_lattices(X39)
      | ~ v4_lattice3(X39)
      | ~ l3_lattices(X39)
      | ~ m1_subset_1(X40,u1_struct_0(X39))
      | ~ r2_hidden(X40,X41)
      | ~ r3_lattice3(X39,X40,X41)
      | k16_lattice3(X39,X41) = X40 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_lattice3])])])])).

cnf(c_0_67,negated_conjecture,
    ( r3_lattice3(esk4_0,esk5_0,k1_tarski(X1))
    | ~ r4_lattice3(esk4_0,X1,X2)
    | ~ r2_hidden(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_40]),c_0_53])).

cnf(c_0_68,negated_conjecture,
    ( r4_lattice3(esk4_0,esk5_0,k1_tarski(X1))
    | ~ r1_lattices(esk4_0,X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_20]),c_0_24])]),c_0_25])).

cnf(c_0_69,negated_conjecture,
    ( r1_lattices(esk4_0,X1,esk5_0)
    | ~ r3_lattices(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_20]),c_0_57]),c_0_58]),c_0_59]),c_0_24])]),c_0_25])).

cnf(c_0_70,negated_conjecture,
    ( r3_lattices(esk4_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_20]),c_0_57]),c_0_58]),c_0_59]),c_0_24])]),c_0_25])).

cnf(c_0_71,negated_conjecture,
    ( k15_lattice3(esk4_0,k1_tarski(esk5_0)) != esk5_0
    | k16_lattice3(esk4_0,k1_tarski(esk5_0)) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_24])])).

cnf(c_0_72,negated_conjecture,
    ( k15_lattice3(esk4_0,X1) = esk5_0
    | ~ r4_lattice3(esk4_0,esk5_0,X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_20]),c_0_64]),c_0_44]),c_0_24])]),c_0_25])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_65])])).

cnf(c_0_74,plain,
    ( v2_struct_0(X1)
    | k16_lattice3(X1,X3) = X2
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X3)
    | ~ r3_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( r3_lattice3(esk4_0,esk5_0,k1_tarski(esk5_0))
    | ~ r1_lattices(esk4_0,X1,esk5_0)
    | ~ r2_hidden(esk5_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( r1_lattices(esk4_0,esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_20])])).

cnf(c_0_77,negated_conjecture,
    ( k16_lattice3(esk4_0,k1_tarski(esk5_0)) != esk5_0
    | ~ r4_lattice3(esk4_0,esk5_0,k1_tarski(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])])).

cnf(c_0_78,negated_conjecture,
    ( k16_lattice3(esk4_0,X1) = esk5_0
    | ~ r2_hidden(esk5_0,X1)
    | ~ r3_lattice3(esk4_0,esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_20]),c_0_64]),c_0_44]),c_0_24])]),c_0_25])).

cnf(c_0_79,negated_conjecture,
    ( r3_lattice3(esk4_0,esk5_0,k1_tarski(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_73])])).

cnf(c_0_80,negated_conjecture,
    ( ~ r4_lattice3(esk4_0,esk5_0,k1_tarski(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_73]),c_0_79])])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_68]),c_0_76])]),
    [proof]).

%------------------------------------------------------------------------------
