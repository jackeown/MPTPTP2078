%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:09 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  118 (11601 expanded)
%              Number of clauses        :   91 (4090 expanded)
%              Number of leaves         :   13 (2820 expanded)
%              Depth                    :   24
%              Number of atoms          :  490 (75062 expanded)
%              Number of equality atoms :   99 (7046 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1)
        & k5_lattices(X1) = k15_lattice3(X1,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(t45_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( X2 = k15_lattice3(X1,a_2_3_lattice3(X1,X2))
            & X2 = k16_lattice3(X1,a_2_4_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(t46_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => ( r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
            & r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).

fof(d13_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v13_lattices(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( k2_lattices(X1,X2,X3) = X2
                  & k2_lattices(X1,X3,X2) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(d6_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v6_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d16_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v13_lattices(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( X2 = k5_lattices(X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( k2_lattices(X1,X2,X3) = X2
                    & k2_lattices(X1,X3,X2) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(t21_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k2_lattices(X1,X2,X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v13_lattices(X1)
          & l3_lattices(X1)
          & k5_lattices(X1) = k15_lattice3(X1,k1_xboole_0) ) ) ),
    inference(assume_negation,[status(cth)],[t50_lattice3])).

fof(c_0_14,plain,(
    ! [X11] :
      ( ( l1_lattices(X11)
        | ~ l3_lattices(X11) )
      & ( l2_lattices(X11)
        | ~ l3_lattices(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v10_lattices(esk6_0)
    & v4_lattice3(esk6_0)
    & l3_lattices(esk6_0)
    & ( v2_struct_0(esk6_0)
      | ~ v10_lattices(esk6_0)
      | ~ v13_lattices(esk6_0)
      | ~ l3_lattices(esk6_0)
      | k5_lattices(esk6_0) != k15_lattice3(esk6_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X30,X31] :
      ( ( X31 = k15_lattice3(X30,a_2_3_lattice3(X30,X31))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v4_lattice3(X30)
        | ~ l3_lattices(X30) )
      & ( X31 = k16_lattice3(X30,a_2_4_lattice3(X30,X31))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v4_lattice3(X30)
        | ~ l3_lattices(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).

fof(c_0_17,plain,(
    ! [X10] :
      ( v2_struct_0(X10)
      | ~ l1_lattices(X10)
      | m1_subset_1(k5_lattices(X10),u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

cnf(c_0_18,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( l3_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( X1 = k15_lattice3(X2,a_2_3_lattice3(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v4_lattice3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v10_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( l1_lattices(esk6_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_26,plain,(
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

fof(c_0_27,plain,(
    ! [X32,X33,X34] :
      ( ( r3_lattices(X32,k15_lattice3(X32,X33),k15_lattice3(X32,X34))
        | ~ r1_tarski(X33,X34)
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ v4_lattice3(X32)
        | ~ l3_lattices(X32) )
      & ( r3_lattices(X32,k16_lattice3(X32,X34),k16_lattice3(X32,X33))
        | ~ r1_tarski(X33,X34)
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ v4_lattice3(X32)
        | ~ l3_lattices(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_lattice3])])])])])).

cnf(c_0_28,negated_conjecture,
    ( k15_lattice3(esk6_0,a_2_3_lattice3(esk6_0,X1)) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_19])]),c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk6_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_23])).

fof(c_0_30,plain,(
    ! [X18,X20,X21] :
      ( ( m1_subset_1(esk2_1(X18),u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) )
      & ( k2_lattices(X18,esk2_1(X18),X20) = esk2_1(X18)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) )
      & ( k2_lattices(X18,X20,esk2_1(X18)) = esk2_1(X18)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) )
      & ( m1_subset_1(esk3_2(X18,X21),u1_struct_0(X18))
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) )
      & ( k2_lattices(X18,X21,esk3_2(X18,X21)) != X21
        | k2_lattices(X18,esk3_2(X18,X21),X21) != X21
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

fof(c_0_31,plain,(
    ! [X28,X29] :
      ( v2_struct_0(X28)
      | ~ l3_lattices(X28)
      | m1_subset_1(k15_lattice3(X28,X29),u1_struct_0(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_32,plain,(
    ! [X23,X24,X25] :
      ( ( ~ v6_lattices(X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | k2_lattices(X23,X24,X25) = k2_lattices(X23,X25,X24)
        | v2_struct_0(X23)
        | ~ l1_lattices(X23) )
      & ( m1_subset_1(esk4_1(X23),u1_struct_0(X23))
        | v6_lattices(X23)
        | v2_struct_0(X23)
        | ~ l1_lattices(X23) )
      & ( m1_subset_1(esk5_1(X23),u1_struct_0(X23))
        | v6_lattices(X23)
        | v2_struct_0(X23)
        | ~ l1_lattices(X23) )
      & ( k2_lattices(X23,esk4_1(X23),esk5_1(X23)) != k2_lattices(X23,esk5_1(X23),esk4_1(X23))
        | v6_lattices(X23)
        | v2_struct_0(X23)
        | ~ l1_lattices(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

cnf(c_0_33,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X12,X13,X14] :
      ( ( ~ r3_lattices(X12,X13,X14)
        | r1_lattices(X12,X13,X14)
        | v2_struct_0(X12)
        | ~ v6_lattices(X12)
        | ~ v8_lattices(X12)
        | ~ v9_lattices(X12)
        | ~ l3_lattices(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12)) )
      & ( ~ r1_lattices(X12,X13,X14)
        | r3_lattices(X12,X13,X14)
        | v2_struct_0(X12)
        | ~ v6_lattices(X12)
        | ~ v8_lattices(X12)
        | ~ v9_lattices(X12)
        | ~ l3_lattices(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_35,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_tarski(X2,X3)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( k15_lattice3(esk6_0,a_2_3_lattice3(esk6_0,k5_lattices(esk6_0))) = k5_lattices(esk6_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_39,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_40,plain,(
    ! [X6,X7,X8] :
      ( ( k2_lattices(X6,X7,X8) = X7
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | X7 != k5_lattices(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v13_lattices(X6)
        | v2_struct_0(X6)
        | ~ l1_lattices(X6) )
      & ( k2_lattices(X6,X8,X7) = X7
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | X7 != k5_lattices(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v13_lattices(X6)
        | v2_struct_0(X6)
        | ~ l1_lattices(X6) )
      & ( m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))
        | X7 = k5_lattices(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v13_lattices(X6)
        | v2_struct_0(X6)
        | ~ l1_lattices(X6) )
      & ( k2_lattices(X6,X7,esk1_2(X6,X7)) != X7
        | k2_lattices(X6,esk1_2(X6,X7),X7) != X7
        | X7 = k5_lattices(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v13_lattices(X6)
        | v2_struct_0(X6)
        | ~ l1_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( v6_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_22]),c_0_19])]),c_0_23])).

fof(c_0_45,plain,(
    ! [X15,X16,X17] :
      ( ( ~ r1_lattices(X15,X16,X17)
        | k2_lattices(X15,X16,X17) = X16
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v8_lattices(X15)
        | ~ v9_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( k2_lattices(X15,X16,X17) != X16
        | r1_lattices(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v8_lattices(X15)
        | ~ v9_lattices(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_46,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( v9_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_22]),c_0_19])]),c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( v8_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_22]),c_0_19])]),c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( r3_lattices(esk6_0,k15_lattice3(esk6_0,X1),k5_lattices(esk6_0))
    | ~ r1_tarski(X1,a_2_3_lattice3(esk6_0,k5_lattices(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_21]),c_0_22]),c_0_19])]),c_0_23])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))
    | v13_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_25]),c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk6_0,X1),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_19]),c_0_23])).

cnf(c_0_54,negated_conjecture,
    ( k2_lattices(esk6_0,X1,X2) = k2_lattices(esk6_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_25]),c_0_44])]),c_0_23])).

cnf(c_0_55,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( r1_lattices(esk6_0,X1,X2)
    | ~ r3_lattices(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_44]),c_0_19])]),c_0_23])).

cnf(c_0_57,negated_conjecture,
    ( r3_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),k5_lattices(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_51]),c_0_24])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk3_2(esk6_0,k15_lattice3(esk6_0,X1)),u1_struct_0(esk6_0))
    | v13_lattices(esk6_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( k2_lattices(esk6_0,X1,k5_lattices(esk6_0)) = k2_lattices(esk6_0,k5_lattices(esk6_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_29])).

cnf(c_0_61,negated_conjecture,
    ( k2_lattices(esk6_0,X1,X2) = X1
    | ~ r1_lattices(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_47]),c_0_48]),c_0_19])]),c_0_23])).

cnf(c_0_62,negated_conjecture,
    ( r1_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),k5_lattices(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_29]),c_0_53])])).

cnf(c_0_63,negated_conjecture,
    ( k2_lattices(esk6_0,X1,k5_lattices(esk6_0)) = k5_lattices(esk6_0)
    | m1_subset_1(esk3_2(esk6_0,k15_lattice3(esk6_0,X2)),u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_25])]),c_0_23])).

cnf(c_0_64,negated_conjecture,
    ( k2_lattices(esk6_0,k15_lattice3(esk6_0,X1),k5_lattices(esk6_0)) = k2_lattices(esk6_0,k5_lattices(esk6_0),k15_lattice3(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( k2_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),k5_lattices(esk6_0)) = k15_lattice3(esk6_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_29]),c_0_53])])).

cnf(c_0_66,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X3) != X2
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_67,negated_conjecture,
    ( k2_lattices(esk6_0,k5_lattices(esk6_0),k15_lattice3(esk6_0,X1)) = k5_lattices(esk6_0)
    | m1_subset_1(esk3_2(esk6_0,k15_lattice3(esk6_0,X2)),u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_53]),c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( k2_lattices(esk6_0,k5_lattices(esk6_0),k15_lattice3(esk6_0,k1_xboole_0)) = k15_lattice3(esk6_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_65,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( r1_lattices(esk6_0,X1,X2)
    | k2_lattices(esk6_0,X1,X2) != X1
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_47]),c_0_48]),c_0_19])]),c_0_23])).

cnf(c_0_70,negated_conjecture,
    ( k15_lattice3(esk6_0,a_2_3_lattice3(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,X1)))) = esk3_2(esk6_0,k15_lattice3(esk6_0,X1))
    | k2_lattices(esk6_0,k5_lattices(esk6_0),k15_lattice3(esk6_0,X2)) = k5_lattices(esk6_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( v2_struct_0(esk6_0)
    | ~ v10_lattices(esk6_0)
    | ~ v13_lattices(esk6_0)
    | ~ l3_lattices(esk6_0)
    | k5_lattices(esk6_0) != k15_lattice3(esk6_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_72,negated_conjecture,
    ( r3_lattices(esk6_0,k15_lattice3(esk6_0,X1),k15_lattice3(esk6_0,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_21]),c_0_22]),c_0_19])]),c_0_23])).

cnf(c_0_73,negated_conjecture,
    ( k15_lattice3(esk6_0,k1_xboole_0) = k5_lattices(esk6_0)
    | ~ r1_lattices(esk6_0,k5_lattices(esk6_0),k15_lattice3(esk6_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_68]),c_0_53]),c_0_29])])).

cnf(c_0_74,negated_conjecture,
    ( k15_lattice3(esk6_0,a_2_3_lattice3(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,X1)))) = esk3_2(esk6_0,k15_lattice3(esk6_0,X1))
    | r1_lattices(esk6_0,k5_lattices(esk6_0),k15_lattice3(esk6_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_53]),c_0_29])])).

cnf(c_0_75,negated_conjecture,
    ( k15_lattice3(esk6_0,k1_xboole_0) != k5_lattices(esk6_0)
    | ~ v13_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_19]),c_0_22])]),c_0_23])).

cnf(c_0_76,plain,
    ( k2_lattices(X1,esk2_1(X1),X2) = esk2_1(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_77,negated_conjecture,
    ( r3_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),k15_lattice3(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_50])).

cnf(c_0_78,negated_conjecture,
    ( k15_lattice3(esk6_0,a_2_3_lattice3(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,X1)))) = esk3_2(esk6_0,k15_lattice3(esk6_0,X1))
    | k15_lattice3(esk6_0,k1_xboole_0) = k5_lattices(esk6_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk3_2(esk6_0,k15_lattice3(esk6_0,X1)),u1_struct_0(esk6_0))
    | k15_lattice3(esk6_0,k1_xboole_0) != k5_lattices(esk6_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_59])).

cnf(c_0_80,negated_conjecture,
    ( k2_lattices(esk6_0,esk2_1(esk6_0),X1) = esk2_1(esk6_0)
    | m1_subset_1(esk3_2(esk6_0,k15_lattice3(esk6_0,X2)),u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_59]),c_0_25])]),c_0_23])).

cnf(c_0_81,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | k2_lattices(X1,esk3_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_82,negated_conjecture,
    ( r1_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),k15_lattice3(esk6_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_77]),c_0_53]),c_0_53])])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk3_2(esk6_0,k15_lattice3(esk6_0,X1)),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_78]),c_0_19])]),c_0_23]),c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( k2_lattices(esk6_0,X1,k15_lattice3(esk6_0,X2)) = k2_lattices(esk6_0,k15_lattice3(esk6_0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_53])).

cnf(c_0_85,negated_conjecture,
    ( k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0)) = esk2_1(esk6_0)
    | m1_subset_1(esk3_2(esk6_0,k15_lattice3(esk6_0,X1)),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_29])).

cnf(c_0_86,negated_conjecture,
    ( v13_lattices(esk6_0)
    | k2_lattices(esk6_0,X1,esk3_2(esk6_0,X1)) != X1
    | k2_lattices(esk6_0,esk3_2(esk6_0,X1),X1) != X1
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_25]),c_0_23])).

cnf(c_0_87,negated_conjecture,
    ( k2_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),k15_lattice3(esk6_0,X1)) = k15_lattice3(esk6_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_82]),c_0_53]),c_0_53])])).

cnf(c_0_88,negated_conjecture,
    ( k15_lattice3(esk6_0,a_2_3_lattice3(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,X1)))) = esk3_2(esk6_0,k15_lattice3(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( k2_lattices(esk6_0,k15_lattice3(esk6_0,X1),k15_lattice3(esk6_0,X2)) = k2_lattices(esk6_0,k15_lattice3(esk6_0,X2),k15_lattice3(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_53])).

cnf(c_0_90,negated_conjecture,
    ( k15_lattice3(esk6_0,a_2_3_lattice3(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,X1)))) = esk3_2(esk6_0,k15_lattice3(esk6_0,X1))
    | k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0)) = esk2_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( v13_lattices(esk6_0)
    | k2_lattices(esk6_0,k15_lattice3(esk6_0,X1),esk3_2(esk6_0,k15_lattice3(esk6_0,X1))) != k15_lattice3(esk6_0,X1)
    | k2_lattices(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,X1)),k15_lattice3(esk6_0,X1)) != k15_lattice3(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_53])).

cnf(c_0_92,negated_conjecture,
    ( k2_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),esk3_2(esk6_0,k15_lattice3(esk6_0,X1))) = k15_lattice3(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( k2_lattices(esk6_0,k15_lattice3(esk6_0,X1),k15_lattice3(esk6_0,k1_xboole_0)) = k15_lattice3(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( k2_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),esk3_2(esk6_0,k15_lattice3(esk6_0,X1))) = k15_lattice3(esk6_0,k1_xboole_0)
    | k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0)) = esk2_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( v13_lattices(esk6_0)
    | k2_lattices(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,k1_xboole_0)),k15_lattice3(esk6_0,k1_xboole_0)) != k15_lattice3(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( k2_lattices(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,X1)),k15_lattice3(esk6_0,k1_xboole_0)) = k15_lattice3(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0)) = esk2_1(esk6_0)
    | v13_lattices(esk6_0)
    | k2_lattices(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,k1_xboole_0)),k15_lattice3(esk6_0,k1_xboole_0)) != k15_lattice3(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( k2_lattices(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,X1)),k15_lattice3(esk6_0,k1_xboole_0)) = k15_lattice3(esk6_0,k1_xboole_0)
    | k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0)) = esk2_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_90])).

cnf(c_0_99,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_100,negated_conjecture,
    ( v13_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96])])).

cnf(c_0_101,negated_conjecture,
    ( k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0)) = esk2_1(esk6_0)
    | v13_lattices(esk6_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(esk2_1(esk6_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_25])]),c_0_23])).

cnf(c_0_103,plain,
    ( k2_lattices(X1,X2,esk2_1(X1)) = esk2_1(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_104,negated_conjecture,
    ( k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0)) = esk2_1(esk6_0)
    | m1_subset_1(esk2_1(esk6_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_101]),c_0_25])]),c_0_23])).

cnf(c_0_105,negated_conjecture,
    ( k15_lattice3(esk6_0,a_2_3_lattice3(esk6_0,esk2_1(esk6_0))) = esk2_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( k2_lattices(esk6_0,X1,esk2_1(esk6_0)) = esk2_1(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_100]),c_0_25])]),c_0_23])).

cnf(c_0_107,negated_conjecture,
    ( k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0)) = k2_lattices(esk6_0,k5_lattices(esk6_0),esk2_1(esk6_0))
    | k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0)) = esk2_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_104])).

cnf(c_0_108,negated_conjecture,
    ( k2_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),esk2_1(esk6_0)) = k15_lattice3(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( k2_lattices(esk6_0,k15_lattice3(esk6_0,X1),esk2_1(esk6_0)) = esk2_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_53])).

cnf(c_0_110,negated_conjecture,
    ( k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0)) = esk2_1(esk6_0)
    | k2_lattices(esk6_0,k5_lattices(esk6_0),esk2_1(esk6_0)) != esk2_1(esk6_0) ),
    inference(ef,[status(thm)],[c_0_107])).

cnf(c_0_111,negated_conjecture,
    ( k2_lattices(esk6_0,k5_lattices(esk6_0),esk2_1(esk6_0)) = esk2_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_29])).

cnf(c_0_112,negated_conjecture,
    ( k15_lattice3(esk6_0,k1_xboole_0) != k5_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_100])])).

cnf(c_0_113,negated_conjecture,
    ( k15_lattice3(esk6_0,k1_xboole_0) = esk2_1(esk6_0) ),
    inference(rw,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_114,negated_conjecture,
    ( k2_lattices(esk6_0,X1,k5_lattices(esk6_0)) = k5_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_100]),c_0_25])]),c_0_23])).

cnf(c_0_115,negated_conjecture,
    ( k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0)) = esk2_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_111])])).

cnf(c_0_116,negated_conjecture,
    ( esk2_1(esk6_0) != k5_lattices(esk6_0) ),
    inference(rw,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_117,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_102]),c_0_115]),c_0_116]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 0.19/0.47  # and selection function HSelectMinInfpos.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.029 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 0.19/0.47  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.19/0.47  fof(t45_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k15_lattice3(X1,a_2_3_lattice3(X1,X2))&X2=k16_lattice3(X1,a_2_4_lattice3(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_lattice3)).
% 0.19/0.47  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.19/0.47  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.19/0.47  fof(t46_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_lattice3)).
% 0.19/0.47  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 0.19/0.47  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.19/0.47  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 0.19/0.47  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.19/0.47  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.47  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 0.19/0.47  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 0.19/0.47  fof(c_0_13, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 0.19/0.47  fof(c_0_14, plain, ![X11]:((l1_lattices(X11)|~l3_lattices(X11))&(l2_lattices(X11)|~l3_lattices(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.19/0.47  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk6_0)&v10_lattices(esk6_0))&v4_lattice3(esk6_0))&l3_lattices(esk6_0))&(v2_struct_0(esk6_0)|~v10_lattices(esk6_0)|~v13_lattices(esk6_0)|~l3_lattices(esk6_0)|k5_lattices(esk6_0)!=k15_lattice3(esk6_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.19/0.47  fof(c_0_16, plain, ![X30, X31]:((X31=k15_lattice3(X30,a_2_3_lattice3(X30,X31))|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v4_lattice3(X30)|~l3_lattices(X30)))&(X31=k16_lattice3(X30,a_2_4_lattice3(X30,X31))|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v4_lattice3(X30)|~l3_lattices(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).
% 0.19/0.47  fof(c_0_17, plain, ![X10]:(v2_struct_0(X10)|~l1_lattices(X10)|m1_subset_1(k5_lattices(X10),u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.19/0.47  cnf(c_0_18, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  cnf(c_0_19, negated_conjecture, (l3_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.47  cnf(c_0_20, plain, (X1=k15_lattice3(X2,a_2_3_lattice3(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.47  cnf(c_0_21, negated_conjecture, (v4_lattice3(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.47  cnf(c_0_22, negated_conjecture, (v10_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.47  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.47  cnf(c_0_24, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.47  cnf(c_0_25, negated_conjecture, (l1_lattices(esk6_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.47  fof(c_0_26, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.19/0.47  fof(c_0_27, plain, ![X32, X33, X34]:((r3_lattices(X32,k15_lattice3(X32,X33),k15_lattice3(X32,X34))|~r1_tarski(X33,X34)|(v2_struct_0(X32)|~v10_lattices(X32)|~v4_lattice3(X32)|~l3_lattices(X32)))&(r3_lattices(X32,k16_lattice3(X32,X34),k16_lattice3(X32,X33))|~r1_tarski(X33,X34)|(v2_struct_0(X32)|~v10_lattices(X32)|~v4_lattice3(X32)|~l3_lattices(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_lattice3])])])])])).
% 0.19/0.47  cnf(c_0_28, negated_conjecture, (k15_lattice3(esk6_0,a_2_3_lattice3(esk6_0,X1))=X1|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_19])]), c_0_23])).
% 0.19/0.47  cnf(c_0_29, negated_conjecture, (m1_subset_1(k5_lattices(esk6_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_23])).
% 0.19/0.47  fof(c_0_30, plain, ![X18, X20, X21]:(((m1_subset_1(esk2_1(X18),u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18)))&((k2_lattices(X18,esk2_1(X18),X20)=esk2_1(X18)|~m1_subset_1(X20,u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18)))&(k2_lattices(X18,X20,esk2_1(X18))=esk2_1(X18)|~m1_subset_1(X20,u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18)))))&((m1_subset_1(esk3_2(X18,X21),u1_struct_0(X18))|~m1_subset_1(X21,u1_struct_0(X18))|v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18)))&(k2_lattices(X18,X21,esk3_2(X18,X21))!=X21|k2_lattices(X18,esk3_2(X18,X21),X21)!=X21|~m1_subset_1(X21,u1_struct_0(X18))|v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 0.19/0.47  fof(c_0_31, plain, ![X28, X29]:(v2_struct_0(X28)|~l3_lattices(X28)|m1_subset_1(k15_lattice3(X28,X29),u1_struct_0(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.19/0.47  fof(c_0_32, plain, ![X23, X24, X25]:((~v6_lattices(X23)|(~m1_subset_1(X24,u1_struct_0(X23))|(~m1_subset_1(X25,u1_struct_0(X23))|k2_lattices(X23,X24,X25)=k2_lattices(X23,X25,X24)))|(v2_struct_0(X23)|~l1_lattices(X23)))&((m1_subset_1(esk4_1(X23),u1_struct_0(X23))|v6_lattices(X23)|(v2_struct_0(X23)|~l1_lattices(X23)))&((m1_subset_1(esk5_1(X23),u1_struct_0(X23))|v6_lattices(X23)|(v2_struct_0(X23)|~l1_lattices(X23)))&(k2_lattices(X23,esk4_1(X23),esk5_1(X23))!=k2_lattices(X23,esk5_1(X23),esk4_1(X23))|v6_lattices(X23)|(v2_struct_0(X23)|~l1_lattices(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 0.19/0.47  cnf(c_0_33, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.47  fof(c_0_34, plain, ![X12, X13, X14]:((~r3_lattices(X12,X13,X14)|r1_lattices(X12,X13,X14)|(v2_struct_0(X12)|~v6_lattices(X12)|~v8_lattices(X12)|~v9_lattices(X12)|~l3_lattices(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))))&(~r1_lattices(X12,X13,X14)|r3_lattices(X12,X13,X14)|(v2_struct_0(X12)|~v6_lattices(X12)|~v8_lattices(X12)|~v9_lattices(X12)|~l3_lattices(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.19/0.47  cnf(c_0_35, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.47  cnf(c_0_36, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.47  cnf(c_0_37, plain, (r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~r1_tarski(X2,X3)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.47  cnf(c_0_38, negated_conjecture, (k15_lattice3(esk6_0,a_2_3_lattice3(esk6_0,k5_lattices(esk6_0)))=k5_lattices(esk6_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.47  fof(c_0_39, plain, ![X4]:r1_tarski(k1_xboole_0,X4), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.47  fof(c_0_40, plain, ![X6, X7, X8]:(((k2_lattices(X6,X7,X8)=X7|~m1_subset_1(X8,u1_struct_0(X6))|X7!=k5_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~v13_lattices(X6)|(v2_struct_0(X6)|~l1_lattices(X6)))&(k2_lattices(X6,X8,X7)=X7|~m1_subset_1(X8,u1_struct_0(X6))|X7!=k5_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~v13_lattices(X6)|(v2_struct_0(X6)|~l1_lattices(X6))))&((m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))|X7=k5_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~v13_lattices(X6)|(v2_struct_0(X6)|~l1_lattices(X6)))&(k2_lattices(X6,X7,esk1_2(X6,X7))!=X7|k2_lattices(X6,esk1_2(X6,X7),X7)!=X7|X7=k5_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~v13_lattices(X6)|(v2_struct_0(X6)|~l1_lattices(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.19/0.47  cnf(c_0_41, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.47  cnf(c_0_42, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.47  cnf(c_0_43, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.47  cnf(c_0_44, negated_conjecture, (v6_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_22]), c_0_19])]), c_0_23])).
% 0.19/0.47  fof(c_0_45, plain, ![X15, X16, X17]:((~r1_lattices(X15,X16,X17)|k2_lattices(X15,X16,X17)=X16|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~v8_lattices(X15)|~v9_lattices(X15)|~l3_lattices(X15)))&(k2_lattices(X15,X16,X17)!=X16|r1_lattices(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~v8_lattices(X15)|~v9_lattices(X15)|~l3_lattices(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.19/0.47  cnf(c_0_46, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.47  cnf(c_0_47, negated_conjecture, (v9_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_22]), c_0_19])]), c_0_23])).
% 0.19/0.47  cnf(c_0_48, negated_conjecture, (v8_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_22]), c_0_19])]), c_0_23])).
% 0.19/0.47  cnf(c_0_49, negated_conjecture, (r3_lattices(esk6_0,k15_lattice3(esk6_0,X1),k5_lattices(esk6_0))|~r1_tarski(X1,a_2_3_lattice3(esk6_0,k5_lattices(esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_21]), c_0_22]), c_0_19])]), c_0_23])).
% 0.19/0.47  cnf(c_0_50, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.47  cnf(c_0_51, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.47  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk3_2(esk6_0,X1),u1_struct_0(esk6_0))|v13_lattices(esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_25]), c_0_23])).
% 0.19/0.47  cnf(c_0_53, negated_conjecture, (m1_subset_1(k15_lattice3(esk6_0,X1),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_19]), c_0_23])).
% 0.19/0.47  cnf(c_0_54, negated_conjecture, (k2_lattices(esk6_0,X1,X2)=k2_lattices(esk6_0,X2,X1)|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_25]), c_0_44])]), c_0_23])).
% 0.19/0.47  cnf(c_0_55, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.47  cnf(c_0_56, negated_conjecture, (r1_lattices(esk6_0,X1,X2)|~r3_lattices(esk6_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_44]), c_0_19])]), c_0_23])).
% 0.19/0.47  cnf(c_0_57, negated_conjecture, (r3_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),k5_lattices(esk6_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.47  cnf(c_0_58, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_51]), c_0_24])).
% 0.19/0.47  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk3_2(esk6_0,k15_lattice3(esk6_0,X1)),u1_struct_0(esk6_0))|v13_lattices(esk6_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.47  cnf(c_0_60, negated_conjecture, (k2_lattices(esk6_0,X1,k5_lattices(esk6_0))=k2_lattices(esk6_0,k5_lattices(esk6_0),X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_54, c_0_29])).
% 0.19/0.47  cnf(c_0_61, negated_conjecture, (k2_lattices(esk6_0,X1,X2)=X1|~r1_lattices(esk6_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_47]), c_0_48]), c_0_19])]), c_0_23])).
% 0.19/0.47  cnf(c_0_62, negated_conjecture, (r1_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),k5_lattices(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_29]), c_0_53])])).
% 0.19/0.47  cnf(c_0_63, negated_conjecture, (k2_lattices(esk6_0,X1,k5_lattices(esk6_0))=k5_lattices(esk6_0)|m1_subset_1(esk3_2(esk6_0,k15_lattice3(esk6_0,X2)),u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_25])]), c_0_23])).
% 0.19/0.47  cnf(c_0_64, negated_conjecture, (k2_lattices(esk6_0,k15_lattice3(esk6_0,X1),k5_lattices(esk6_0))=k2_lattices(esk6_0,k5_lattices(esk6_0),k15_lattice3(esk6_0,X1))), inference(spm,[status(thm)],[c_0_60, c_0_53])).
% 0.19/0.47  cnf(c_0_65, negated_conjecture, (k2_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),k5_lattices(esk6_0))=k15_lattice3(esk6_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_29]), c_0_53])])).
% 0.19/0.47  cnf(c_0_66, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k2_lattices(X1,X2,X3)!=X2|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.47  cnf(c_0_67, negated_conjecture, (k2_lattices(esk6_0,k5_lattices(esk6_0),k15_lattice3(esk6_0,X1))=k5_lattices(esk6_0)|m1_subset_1(esk3_2(esk6_0,k15_lattice3(esk6_0,X2)),u1_struct_0(esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_53]), c_0_64])).
% 0.19/0.47  cnf(c_0_68, negated_conjecture, (k2_lattices(esk6_0,k5_lattices(esk6_0),k15_lattice3(esk6_0,k1_xboole_0))=k15_lattice3(esk6_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_65, c_0_64])).
% 0.19/0.47  cnf(c_0_69, negated_conjecture, (r1_lattices(esk6_0,X1,X2)|k2_lattices(esk6_0,X1,X2)!=X1|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_47]), c_0_48]), c_0_19])]), c_0_23])).
% 0.19/0.47  cnf(c_0_70, negated_conjecture, (k15_lattice3(esk6_0,a_2_3_lattice3(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,X1))))=esk3_2(esk6_0,k15_lattice3(esk6_0,X1))|k2_lattices(esk6_0,k5_lattices(esk6_0),k15_lattice3(esk6_0,X2))=k5_lattices(esk6_0)), inference(spm,[status(thm)],[c_0_28, c_0_67])).
% 0.19/0.47  cnf(c_0_71, negated_conjecture, (v2_struct_0(esk6_0)|~v10_lattices(esk6_0)|~v13_lattices(esk6_0)|~l3_lattices(esk6_0)|k5_lattices(esk6_0)!=k15_lattice3(esk6_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.47  cnf(c_0_72, negated_conjecture, (r3_lattices(esk6_0,k15_lattice3(esk6_0,X1),k15_lattice3(esk6_0,X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_21]), c_0_22]), c_0_19])]), c_0_23])).
% 0.19/0.47  cnf(c_0_73, negated_conjecture, (k15_lattice3(esk6_0,k1_xboole_0)=k5_lattices(esk6_0)|~r1_lattices(esk6_0,k5_lattices(esk6_0),k15_lattice3(esk6_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_68]), c_0_53]), c_0_29])])).
% 0.19/0.47  cnf(c_0_74, negated_conjecture, (k15_lattice3(esk6_0,a_2_3_lattice3(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,X1))))=esk3_2(esk6_0,k15_lattice3(esk6_0,X1))|r1_lattices(esk6_0,k5_lattices(esk6_0),k15_lattice3(esk6_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_53]), c_0_29])])).
% 0.19/0.47  cnf(c_0_75, negated_conjecture, (k15_lattice3(esk6_0,k1_xboole_0)!=k5_lattices(esk6_0)|~v13_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_19]), c_0_22])]), c_0_23])).
% 0.19/0.47  cnf(c_0_76, plain, (k2_lattices(X1,esk2_1(X1),X2)=esk2_1(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.47  cnf(c_0_77, negated_conjecture, (r3_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),k15_lattice3(esk6_0,X1))), inference(spm,[status(thm)],[c_0_72, c_0_50])).
% 0.19/0.47  cnf(c_0_78, negated_conjecture, (k15_lattice3(esk6_0,a_2_3_lattice3(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,X1))))=esk3_2(esk6_0,k15_lattice3(esk6_0,X1))|k15_lattice3(esk6_0,k1_xboole_0)=k5_lattices(esk6_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.47  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk3_2(esk6_0,k15_lattice3(esk6_0,X1)),u1_struct_0(esk6_0))|k15_lattice3(esk6_0,k1_xboole_0)!=k5_lattices(esk6_0)), inference(spm,[status(thm)],[c_0_75, c_0_59])).
% 0.19/0.47  cnf(c_0_80, negated_conjecture, (k2_lattices(esk6_0,esk2_1(esk6_0),X1)=esk2_1(esk6_0)|m1_subset_1(esk3_2(esk6_0,k15_lattice3(esk6_0,X2)),u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_59]), c_0_25])]), c_0_23])).
% 0.19/0.47  cnf(c_0_81, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|k2_lattices(X1,esk3_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.47  cnf(c_0_82, negated_conjecture, (r1_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),k15_lattice3(esk6_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_77]), c_0_53]), c_0_53])])).
% 0.19/0.47  cnf(c_0_83, negated_conjecture, (m1_subset_1(esk3_2(esk6_0,k15_lattice3(esk6_0,X1)),u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_78]), c_0_19])]), c_0_23]), c_0_79])).
% 0.19/0.47  cnf(c_0_84, negated_conjecture, (k2_lattices(esk6_0,X1,k15_lattice3(esk6_0,X2))=k2_lattices(esk6_0,k15_lattice3(esk6_0,X2),X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_54, c_0_53])).
% 0.19/0.47  cnf(c_0_85, negated_conjecture, (k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0))=esk2_1(esk6_0)|m1_subset_1(esk3_2(esk6_0,k15_lattice3(esk6_0,X1)),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_80, c_0_29])).
% 0.19/0.47  cnf(c_0_86, negated_conjecture, (v13_lattices(esk6_0)|k2_lattices(esk6_0,X1,esk3_2(esk6_0,X1))!=X1|k2_lattices(esk6_0,esk3_2(esk6_0,X1),X1)!=X1|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_25]), c_0_23])).
% 0.19/0.47  cnf(c_0_87, negated_conjecture, (k2_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),k15_lattice3(esk6_0,X1))=k15_lattice3(esk6_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_82]), c_0_53]), c_0_53])])).
% 0.19/0.47  cnf(c_0_88, negated_conjecture, (k15_lattice3(esk6_0,a_2_3_lattice3(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,X1))))=esk3_2(esk6_0,k15_lattice3(esk6_0,X1))), inference(spm,[status(thm)],[c_0_28, c_0_83])).
% 0.19/0.47  cnf(c_0_89, negated_conjecture, (k2_lattices(esk6_0,k15_lattice3(esk6_0,X1),k15_lattice3(esk6_0,X2))=k2_lattices(esk6_0,k15_lattice3(esk6_0,X2),k15_lattice3(esk6_0,X1))), inference(spm,[status(thm)],[c_0_84, c_0_53])).
% 0.19/0.47  cnf(c_0_90, negated_conjecture, (k15_lattice3(esk6_0,a_2_3_lattice3(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,X1))))=esk3_2(esk6_0,k15_lattice3(esk6_0,X1))|k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0))=esk2_1(esk6_0)), inference(spm,[status(thm)],[c_0_28, c_0_85])).
% 0.19/0.47  cnf(c_0_91, negated_conjecture, (v13_lattices(esk6_0)|k2_lattices(esk6_0,k15_lattice3(esk6_0,X1),esk3_2(esk6_0,k15_lattice3(esk6_0,X1)))!=k15_lattice3(esk6_0,X1)|k2_lattices(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,X1)),k15_lattice3(esk6_0,X1))!=k15_lattice3(esk6_0,X1)), inference(spm,[status(thm)],[c_0_86, c_0_53])).
% 0.19/0.47  cnf(c_0_92, negated_conjecture, (k2_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),esk3_2(esk6_0,k15_lattice3(esk6_0,X1)))=k15_lattice3(esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.19/0.47  cnf(c_0_93, negated_conjecture, (k2_lattices(esk6_0,k15_lattice3(esk6_0,X1),k15_lattice3(esk6_0,k1_xboole_0))=k15_lattice3(esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_89])).
% 0.19/0.47  cnf(c_0_94, negated_conjecture, (k2_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),esk3_2(esk6_0,k15_lattice3(esk6_0,X1)))=k15_lattice3(esk6_0,k1_xboole_0)|k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0))=esk2_1(esk6_0)), inference(spm,[status(thm)],[c_0_87, c_0_90])).
% 0.19/0.47  cnf(c_0_95, negated_conjecture, (v13_lattices(esk6_0)|k2_lattices(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,k1_xboole_0)),k15_lattice3(esk6_0,k1_xboole_0))!=k15_lattice3(esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.19/0.47  cnf(c_0_96, negated_conjecture, (k2_lattices(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,X1)),k15_lattice3(esk6_0,k1_xboole_0))=k15_lattice3(esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_93, c_0_88])).
% 0.19/0.47  cnf(c_0_97, negated_conjecture, (k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0))=esk2_1(esk6_0)|v13_lattices(esk6_0)|k2_lattices(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,k1_xboole_0)),k15_lattice3(esk6_0,k1_xboole_0))!=k15_lattice3(esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_91, c_0_94])).
% 0.19/0.47  cnf(c_0_98, negated_conjecture, (k2_lattices(esk6_0,esk3_2(esk6_0,k15_lattice3(esk6_0,X1)),k15_lattice3(esk6_0,k1_xboole_0))=k15_lattice3(esk6_0,k1_xboole_0)|k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0))=esk2_1(esk6_0)), inference(spm,[status(thm)],[c_0_93, c_0_90])).
% 0.19/0.47  cnf(c_0_99, plain, (m1_subset_1(esk2_1(X1),u1_struct_0(X1))|v2_struct_0(X1)|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.47  cnf(c_0_100, negated_conjecture, (v13_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96])])).
% 0.19/0.47  cnf(c_0_101, negated_conjecture, (k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0))=esk2_1(esk6_0)|v13_lattices(esk6_0)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.19/0.47  cnf(c_0_102, negated_conjecture, (m1_subset_1(esk2_1(esk6_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_25])]), c_0_23])).
% 0.19/0.47  cnf(c_0_103, plain, (k2_lattices(X1,X2,esk2_1(X1))=esk2_1(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.47  cnf(c_0_104, negated_conjecture, (k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0))=esk2_1(esk6_0)|m1_subset_1(esk2_1(esk6_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_101]), c_0_25])]), c_0_23])).
% 0.19/0.47  cnf(c_0_105, negated_conjecture, (k15_lattice3(esk6_0,a_2_3_lattice3(esk6_0,esk2_1(esk6_0)))=esk2_1(esk6_0)), inference(spm,[status(thm)],[c_0_28, c_0_102])).
% 0.19/0.47  cnf(c_0_106, negated_conjecture, (k2_lattices(esk6_0,X1,esk2_1(esk6_0))=esk2_1(esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_100]), c_0_25])]), c_0_23])).
% 0.19/0.47  cnf(c_0_107, negated_conjecture, (k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0))=k2_lattices(esk6_0,k5_lattices(esk6_0),esk2_1(esk6_0))|k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0))=esk2_1(esk6_0)), inference(spm,[status(thm)],[c_0_60, c_0_104])).
% 0.19/0.47  cnf(c_0_108, negated_conjecture, (k2_lattices(esk6_0,k15_lattice3(esk6_0,k1_xboole_0),esk2_1(esk6_0))=k15_lattice3(esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_105])).
% 0.19/0.47  cnf(c_0_109, negated_conjecture, (k2_lattices(esk6_0,k15_lattice3(esk6_0,X1),esk2_1(esk6_0))=esk2_1(esk6_0)), inference(spm,[status(thm)],[c_0_106, c_0_53])).
% 0.19/0.47  cnf(c_0_110, negated_conjecture, (k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0))=esk2_1(esk6_0)|k2_lattices(esk6_0,k5_lattices(esk6_0),esk2_1(esk6_0))!=esk2_1(esk6_0)), inference(ef,[status(thm)],[c_0_107])).
% 0.19/0.47  cnf(c_0_111, negated_conjecture, (k2_lattices(esk6_0,k5_lattices(esk6_0),esk2_1(esk6_0))=esk2_1(esk6_0)), inference(spm,[status(thm)],[c_0_106, c_0_29])).
% 0.19/0.47  cnf(c_0_112, negated_conjecture, (k15_lattice3(esk6_0,k1_xboole_0)!=k5_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_100])])).
% 0.19/0.47  cnf(c_0_113, negated_conjecture, (k15_lattice3(esk6_0,k1_xboole_0)=esk2_1(esk6_0)), inference(rw,[status(thm)],[c_0_108, c_0_109])).
% 0.19/0.47  cnf(c_0_114, negated_conjecture, (k2_lattices(esk6_0,X1,k5_lattices(esk6_0))=k5_lattices(esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_100]), c_0_25])]), c_0_23])).
% 0.19/0.47  cnf(c_0_115, negated_conjecture, (k2_lattices(esk6_0,esk2_1(esk6_0),k5_lattices(esk6_0))=esk2_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_111])])).
% 0.19/0.47  cnf(c_0_116, negated_conjecture, (esk2_1(esk6_0)!=k5_lattices(esk6_0)), inference(rw,[status(thm)],[c_0_112, c_0_113])).
% 0.19/0.47  cnf(c_0_117, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_102]), c_0_115]), c_0_116]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 118
% 0.19/0.47  # Proof object clause steps            : 91
% 0.19/0.47  # Proof object formula steps           : 27
% 0.19/0.47  # Proof object conjectures             : 74
% 0.19/0.47  # Proof object clause conjectures      : 71
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 24
% 0.19/0.47  # Proof object initial formulas used   : 13
% 0.19/0.47  # Proof object generating inferences   : 59
% 0.19/0.47  # Proof object simplifying inferences  : 100
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 13
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 38
% 0.19/0.47  # Removed in clause preprocessing      : 1
% 0.19/0.47  # Initial clauses in saturation        : 37
% 0.19/0.47  # Processed clauses                    : 1154
% 0.19/0.47  # ...of these trivial                  : 30
% 0.19/0.47  # ...subsumed                          : 523
% 0.19/0.47  # ...remaining for further processing  : 601
% 0.19/0.47  # Other redundant clauses eliminated   : 2
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 198
% 0.19/0.47  # Backward-rewritten                   : 196
% 0.19/0.47  # Generated clauses                    : 4556
% 0.19/0.47  # ...of the previous two non-trivial   : 4405
% 0.19/0.47  # Contextual simplify-reflections      : 9
% 0.19/0.47  # Paramodulations                      : 4550
% 0.19/0.47  # Factorizations                       : 3
% 0.19/0.47  # Equation resolutions                 : 3
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 168
% 0.19/0.47  #    Positive orientable unit clauses  : 58
% 0.19/0.47  #    Positive unorientable unit clauses: 2
% 0.19/0.47  #    Negative unit clauses             : 3
% 0.19/0.47  #    Non-unit-clauses                  : 105
% 0.19/0.47  # Current number of unprocessed clauses: 2352
% 0.19/0.47  # ...number of literals in the above   : 6827
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 431
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 14856
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 9281
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 585
% 0.19/0.47  # Unit Clause-clause subsumption calls : 2308
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 269
% 0.19/0.47  # BW rewrite match successes           : 48
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 104880
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.125 s
% 0.19/0.47  # System time              : 0.006 s
% 0.19/0.47  # Total time               : 0.131 s
% 0.19/0.47  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
