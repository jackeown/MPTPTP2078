%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:29 EST 2020

% Result     : Theorem 49.95s
% Output     : CNFRefutation 49.95s
% Verified   : 
% Statistics : Number of formulae       :  203 (10515 expanded)
%              Number of clauses        :  156 (3375 expanded)
%              Number of leaves         :   23 (2607 expanded)
%              Depth                    :   21
%              Number of atoms          :  758 (65803 expanded)
%              Number of equality atoms :  148 (8845 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( k4_lattices(X1,X2,X3) = k5_lattices(X1)
              <=> r3_lattices(X1,X2,k7_lattices(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_lattices)).

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

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(t50_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k7_lattices(X1,k4_lattices(X1,X2,X3)) = k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattices)).

fof(dt_k7_lattices,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(cc5_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v17_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v11_lattices(X1)
          & v15_lattices(X1)
          & v16_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_lattices)).

fof(commutativity_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(cc4_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v15_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v13_lattices(X1)
          & v14_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_lattices)).

fof(dt_k6_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => m1_subset_1(k6_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(t43_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v14_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattices(X1,k6_lattices(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).

fof(t47_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattices(X1,k7_lattices(X1,X2),X2) = k5_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattices)).

fof(t49_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k7_lattices(X1,k7_lattices(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_lattices)).

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

fof(t48_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k3_lattices(X1,k7_lattices(X1,X2),X2) = k6_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattices)).

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

fof(t31_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v11_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => k3_lattices(X1,X2,k4_lattices(X1,X3,X4)) = k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X2,X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_lattices)).

fof(t40_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattices(X1,k5_lattices(X1),X2) = k5_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattices)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(d9_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v9_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v17_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( k4_lattices(X1,X2,X3) = k5_lattices(X1)
                <=> r3_lattices(X1,X2,k7_lattices(X1,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_lattices])).

fof(c_0_24,plain,(
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

fof(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v10_lattices(esk4_0)
    & v17_lattices(esk4_0)
    & l3_lattices(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & ( k4_lattices(esk4_0,esk5_0,esk6_0) != k5_lattices(esk4_0)
      | ~ r3_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0)) )
    & ( k4_lattices(esk4_0,esk5_0,esk6_0) = k5_lattices(esk4_0)
      | r3_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).

fof(c_0_26,plain,(
    ! [X11,X12,X13] :
      ( v2_struct_0(X11)
      | ~ v6_lattices(X11)
      | ~ l1_lattices(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | ~ m1_subset_1(X13,u1_struct_0(X11))
      | k4_lattices(X11,X12,X13) = k4_lattices(X11,X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_27,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( v10_lattices(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( l3_lattices(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X64,X65,X66] :
      ( v2_struct_0(X64)
      | ~ v10_lattices(X64)
      | ~ v17_lattices(X64)
      | ~ l3_lattices(X64)
      | ~ m1_subset_1(X65,u1_struct_0(X64))
      | ~ m1_subset_1(X66,u1_struct_0(X64))
      | k7_lattices(X64,k4_lattices(X64,X65,X66)) = k3_lattices(X64,k7_lattices(X64,X65),k7_lattices(X64,X66)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_lattices])])])])).

fof(c_0_32,plain,(
    ! [X31,X32] :
      ( v2_struct_0(X31)
      | ~ l3_lattices(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | m1_subset_1(k7_lattices(X31,X32),u1_struct_0(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( v6_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),c_0_30])).

fof(c_0_36,plain,(
    ! [X33] :
      ( ( l1_lattices(X33)
        | ~ l3_lattices(X33) )
      & ( l2_lattices(X33)
        | ~ l3_lattices(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_37,plain,(
    ! [X7] :
      ( ( ~ v2_struct_0(X7)
        | v2_struct_0(X7)
        | ~ v17_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v11_lattices(X7)
        | v2_struct_0(X7)
        | ~ v17_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v15_lattices(X7)
        | v2_struct_0(X7)
        | ~ v17_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v16_lattices(X7)
        | v2_struct_0(X7)
        | ~ v17_lattices(X7)
        | ~ l3_lattices(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_lattices])])])])).

fof(c_0_38,plain,(
    ! [X8,X9,X10] :
      ( v2_struct_0(X8)
      | ~ v4_lattices(X8)
      | ~ l2_lattices(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | k3_lattices(X8,X9,X10) = k3_lattices(X8,X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | k7_lattices(X1,k4_lattices(X1,X2,X3)) = k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( v17_lattices(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_43,plain,(
    ! [X26,X27,X28] :
      ( v2_struct_0(X26)
      | ~ v6_lattices(X26)
      | ~ l1_lattices(X26)
      | ~ m1_subset_1(X27,u1_struct_0(X26))
      | ~ m1_subset_1(X28,u1_struct_0(X26))
      | m1_subset_1(k4_lattices(X26,X27,X28),u1_struct_0(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

cnf(c_0_44,negated_conjecture,
    ( k4_lattices(esk4_0,X1,esk6_0) = k4_lattices(esk4_0,esk6_0,X1)
    | ~ l1_lattices(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_30]),c_0_35])])).

cnf(c_0_45,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_46,plain,(
    ! [X6] :
      ( ( ~ v2_struct_0(X6)
        | v2_struct_0(X6)
        | ~ v15_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v13_lattices(X6)
        | v2_struct_0(X6)
        | ~ v15_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v14_lattices(X6)
        | v2_struct_0(X6)
        | ~ v15_lattices(X6)
        | ~ l3_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_lattices])])])])).

cnf(c_0_47,plain,
    ( v15_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_48,plain,(
    ! [X30] :
      ( v2_struct_0(X30)
      | ~ l2_lattices(X30)
      | m1_subset_1(k6_lattices(X30),u1_struct_0(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_lattices])])])).

fof(c_0_49,plain,(
    ! [X29] :
      ( v2_struct_0(X29)
      | ~ l1_lattices(X29)
      | m1_subset_1(k5_lattices(X29),u1_struct_0(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k7_lattices(esk4_0,esk6_0)) = k7_lattices(esk4_0,k4_lattices(esk4_0,X1,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_34]),c_0_40]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk4_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_34]),c_0_29])]),c_0_30])).

cnf(c_0_54,negated_conjecture,
    ( v4_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_56,plain,(
    ! [X56,X57] :
      ( v2_struct_0(X56)
      | ~ v10_lattices(X56)
      | ~ v14_lattices(X56)
      | ~ l3_lattices(X56)
      | ~ m1_subset_1(X57,u1_struct_0(X56))
      | k4_lattices(X56,k6_lattices(X56),X57) = X57 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_lattices])])])])).

cnf(c_0_57,negated_conjecture,
    ( k4_lattices(esk4_0,X1,esk6_0) = k4_lattices(esk4_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_29])])).

cnf(c_0_58,plain,
    ( v14_lattices(X1)
    | v2_struct_0(X1)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( v15_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_40]),c_0_29])]),c_0_30])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_62,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_63,plain,(
    ! [X58,X59] :
      ( v2_struct_0(X58)
      | ~ v10_lattices(X58)
      | ~ v17_lattices(X58)
      | ~ l3_lattices(X58)
      | ~ m1_subset_1(X59,u1_struct_0(X58))
      | k4_lattices(X58,k7_lattices(X58,X59),X59) = k5_lattices(X58) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattices])])])])).

fof(c_0_64,plain,(
    ! [X62,X63] :
      ( v2_struct_0(X62)
      | ~ v10_lattices(X62)
      | ~ v17_lattices(X62)
      | ~ l3_lattices(X62)
      | ~ m1_subset_1(X63,u1_struct_0(X62))
      | k7_lattices(X62,k7_lattices(X62,X63)) = X63 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_lattices])])])])).

cnf(c_0_65,negated_conjecture,
    ( k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k7_lattices(esk4_0,esk5_0)) = k7_lattices(esk4_0,k4_lattices(esk4_0,X1,esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_50]),c_0_40]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_66,negated_conjecture,
    ( k3_lattices(esk4_0,k7_lattices(esk4_0,esk6_0),k7_lattices(esk4_0,X1)) = k7_lattices(esk4_0,k4_lattices(esk4_0,X1,esk6_0))
    | ~ m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ l2_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])]),c_0_30])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_50]),c_0_29])]),c_0_30])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk4_0,X1,esk5_0),u1_struct_0(esk4_0))
    | ~ l1_lattices(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_50]),c_0_30]),c_0_35])])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,k6_lattices(X1),X2) = X2
    | ~ v10_lattices(X1)
    | ~ v14_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk4_0,esk6_0,X1),u1_struct_0(esk4_0))
    | ~ l1_lattices(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_57]),c_0_34]),c_0_35])]),c_0_30])).

cnf(c_0_71,negated_conjecture,
    ( v14_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_29])]),c_0_30])).

cnf(c_0_72,plain,
    ( m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_73,plain,(
    ! [X40,X41,X42] :
      ( ( ~ r3_lattices(X40,X41,X42)
        | r1_lattices(X40,X41,X42)
        | v2_struct_0(X40)
        | ~ v6_lattices(X40)
        | ~ v8_lattices(X40)
        | ~ v9_lattices(X40)
        | ~ l3_lattices(X40)
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | ~ m1_subset_1(X42,u1_struct_0(X40)) )
      & ( ~ r1_lattices(X40,X41,X42)
        | r3_lattices(X40,X41,X42)
        | v2_struct_0(X40)
        | ~ v6_lattices(X40)
        | ~ v8_lattices(X40)
        | ~ v9_lattices(X40)
        | ~ l3_lattices(X40)
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | ~ m1_subset_1(X42,u1_struct_0(X40)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_74,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_75,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_76,plain,
    ( m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_45])).

fof(c_0_77,plain,(
    ! [X60,X61] :
      ( v2_struct_0(X60)
      | ~ v10_lattices(X60)
      | ~ v17_lattices(X60)
      | ~ l3_lattices(X60)
      | ~ m1_subset_1(X61,u1_struct_0(X60))
      | k3_lattices(X60,k7_lattices(X60,X61),X61) = k6_lattices(X60) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattices])])])])).

cnf(c_0_78,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,k7_lattices(X1,X2),X2) = k5_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_79,plain,
    ( v2_struct_0(X1)
    | k7_lattices(X1,k7_lattices(X1,X2)) = X2
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))
    | ~ l1_lattices(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_34]),c_0_30]),c_0_35])])).

cnf(c_0_81,negated_conjecture,
    ( k7_lattices(esk4_0,k4_lattices(esk4_0,esk6_0,esk5_0)) = k7_lattices(esk4_0,k4_lattices(esk4_0,esk5_0,esk6_0))
    | ~ l2_lattices(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_34]),c_0_67]),c_0_50])])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk4_0,X1,k4_lattices(esk4_0,X2,esk5_0)),u1_struct_0(esk4_0))
    | ~ l1_lattices(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_68]),c_0_35])]),c_0_30])).

cnf(c_0_83,negated_conjecture,
    ( k4_lattices(esk4_0,k6_lattices(esk4_0),k4_lattices(esk4_0,esk6_0,X1)) = k4_lattices(esk4_0,esk6_0,X1)
    | ~ l1_lattices(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k6_lattices(esk4_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_29]),c_0_30])).

fof(c_0_85,plain,(
    ! [X43,X44,X45] :
      ( ( ~ r1_lattices(X43,X44,X45)
        | k2_lattices(X43,X44,X45) = X44
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | v2_struct_0(X43)
        | ~ v8_lattices(X43)
        | ~ v9_lattices(X43)
        | ~ l3_lattices(X43) )
      & ( k2_lattices(X43,X44,X45) != X44
        | r1_lattices(X43,X44,X45)
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | v2_struct_0(X43)
        | ~ v8_lattices(X43)
        | ~ v9_lattices(X43)
        | ~ l3_lattices(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_86,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_87,negated_conjecture,
    ( v9_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_88,negated_conjecture,
    ( v8_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk4_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_29]),c_0_30])).

cnf(c_0_90,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,k7_lattices(X1,X2),X2) = k6_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_91,negated_conjecture,
    ( k4_lattices(esk4_0,k7_lattices(esk4_0,esk6_0),esk6_0) = k5_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_34]),c_0_40]),c_0_28]),c_0_29])]),c_0_30])).

fof(c_0_92,plain,(
    ! [X50,X51,X52,X53] :
      ( v2_struct_0(X50)
      | ~ v10_lattices(X50)
      | ~ v11_lattices(X50)
      | ~ l3_lattices(X50)
      | ~ m1_subset_1(X51,u1_struct_0(X50))
      | ~ m1_subset_1(X52,u1_struct_0(X50))
      | ~ m1_subset_1(X53,u1_struct_0(X50))
      | k3_lattices(X50,X51,k4_lattices(X50,X52,X53)) = k4_lattices(X50,k3_lattices(X50,X51,X52),k3_lattices(X50,X51,X53)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_lattices])])])])).

cnf(c_0_93,plain,
    ( v11_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_94,negated_conjecture,
    ( k7_lattices(esk4_0,k7_lattices(esk4_0,k4_lattices(esk4_0,X1,esk6_0))) = k4_lattices(esk4_0,X1,esk6_0)
    | ~ l1_lattices(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_40]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_95,negated_conjecture,
    ( k7_lattices(esk4_0,k7_lattices(esk4_0,k4_lattices(esk4_0,esk5_0,esk6_0))) = k4_lattices(esk4_0,esk6_0,esk5_0)
    | ~ m1_subset_1(k4_lattices(esk4_0,esk6_0,esk5_0),u1_struct_0(esk4_0))
    | ~ l2_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_81]),c_0_40]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk4_0,esk6_0,esk5_0),u1_struct_0(esk4_0))
    | ~ l1_lattices(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_34]),c_0_50])])).

cnf(c_0_97,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_98,negated_conjecture,
    ( r1_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))
    | ~ r3_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_53]),c_0_87]),c_0_88]),c_0_35]),c_0_29])]),c_0_30])).

cnf(c_0_99,negated_conjecture,
    ( k4_lattices(esk4_0,esk5_0,esk6_0) = k5_lattices(esk4_0)
    | r3_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_100,negated_conjecture,
    ( k7_lattices(esk4_0,k7_lattices(esk4_0,k5_lattices(esk4_0))) = k5_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_89]),c_0_40]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_101,negated_conjecture,
    ( k7_lattices(esk4_0,k5_lattices(esk4_0)) = k6_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_52]),c_0_91]),c_0_53]),c_0_40]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk4_0,X1,k6_lattices(esk4_0)),u1_struct_0(esk4_0))
    | ~ l1_lattices(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_84]),c_0_35])]),c_0_30])).

cnf(c_0_103,negated_conjecture,
    ( k4_lattices(esk4_0,X1,k6_lattices(esk4_0)) = k4_lattices(esk4_0,k6_lattices(esk4_0),X1)
    | ~ l1_lattices(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_84]),c_0_35])]),c_0_30])).

cnf(c_0_104,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,k4_lattices(X1,X3,X4)) = k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X2,X4))
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_105,negated_conjecture,
    ( v11_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_40]),c_0_29])]),c_0_30])).

fof(c_0_106,plain,(
    ! [X54,X55] :
      ( v2_struct_0(X54)
      | ~ v10_lattices(X54)
      | ~ v13_lattices(X54)
      | ~ l3_lattices(X54)
      | ~ m1_subset_1(X55,u1_struct_0(X54))
      | k4_lattices(X54,k5_lattices(X54),X55) = k5_lattices(X54) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_lattices])])])])).

cnf(c_0_107,negated_conjecture,
    ( k4_lattices(esk4_0,X1,esk5_0) = k4_lattices(esk4_0,esk5_0,X1)
    | ~ l1_lattices(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_50]),c_0_30]),c_0_35])])).

cnf(c_0_108,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_109,negated_conjecture,
    ( k4_lattices(esk4_0,esk6_0,esk5_0) = k4_lattices(esk4_0,esk5_0,esk6_0)
    | ~ l1_lattices(esk4_0)
    | ~ l2_lattices(esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_50])]),c_0_96])).

cnf(c_0_110,negated_conjecture,
    ( k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),esk5_0) = k6_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_50]),c_0_40]),c_0_28]),c_0_29])]),c_0_30])).

fof(c_0_111,plain,(
    ! [X37,X38,X39] :
      ( v2_struct_0(X37)
      | ~ v6_lattices(X37)
      | ~ l1_lattices(X37)
      | ~ m1_subset_1(X38,u1_struct_0(X37))
      | ~ m1_subset_1(X39,u1_struct_0(X37))
      | k4_lattices(X37,X38,X39) = k2_lattices(X37,X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

cnf(c_0_112,negated_conjecture,
    ( k2_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0)) = X1
    | ~ r1_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_53]),c_0_87]),c_0_88]),c_0_29])]),c_0_30])).

cnf(c_0_113,negated_conjecture,
    ( k5_lattices(esk4_0) = k4_lattices(esk4_0,esk5_0,esk6_0)
    | r1_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_50])])).

cnf(c_0_114,negated_conjecture,
    ( k7_lattices(esk4_0,k6_lattices(esk4_0)) = k5_lattices(esk4_0) ),
    inference(rw,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_115,negated_conjecture,
    ( k4_lattices(esk4_0,X1,k4_lattices(esk4_0,X2,k6_lattices(esk4_0))) = k4_lattices(esk4_0,k4_lattices(esk4_0,X2,k6_lattices(esk4_0)),X1)
    | ~ l1_lattices(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_102]),c_0_35])]),c_0_30])).

cnf(c_0_116,negated_conjecture,
    ( k4_lattices(esk4_0,X1,k6_lattices(esk4_0)) = X1
    | ~ l1_lattices(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_103]),c_0_71]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_117,negated_conjecture,
    ( k4_lattices(esk4_0,k3_lattices(esk4_0,X1,X2),k3_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))) = k3_lattices(esk4_0,X1,k4_lattices(esk4_0,X2,k7_lattices(esk4_0,esk6_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_53]),c_0_105]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_118,negated_conjecture,
    ( k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k6_lattices(esk4_0)) = k7_lattices(esk4_0,k4_lattices(esk4_0,X1,k5_lattices(esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_89]),c_0_40]),c_0_28]),c_0_29])]),c_0_30]),c_0_101])).

cnf(c_0_119,negated_conjecture,
    ( k4_lattices(esk4_0,k6_lattices(esk4_0),k7_lattices(esk4_0,esk6_0)) = k7_lattices(esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_53]),c_0_71]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_120,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,k5_lattices(X1),X2) = k5_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_121,negated_conjecture,
    ( k4_lattices(esk4_0,X1,esk5_0) = k4_lattices(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_45]),c_0_29])])).

cnf(c_0_122,negated_conjecture,
    ( v13_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_59]),c_0_29])]),c_0_30])).

cnf(c_0_123,negated_conjecture,
    ( k4_lattices(esk4_0,esk6_0,esk5_0) = k4_lattices(esk4_0,esk5_0,esk6_0)
    | ~ l1_lattices(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_61]),c_0_29])])).

cnf(c_0_124,negated_conjecture,
    ( k4_lattices(esk4_0,k6_lattices(esk4_0),k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),X1)) = k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k4_lattices(esk4_0,esk5_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_110]),c_0_50]),c_0_67]),c_0_105]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_125,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_126,negated_conjecture,
    ( k2_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0)) = esk5_0
    | k5_lattices(esk4_0) = k4_lattices(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_50])])).

cnf(c_0_127,negated_conjecture,
    ( k7_lattices(esk4_0,k4_lattices(esk4_0,X1,k6_lattices(esk4_0))) = k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k5_lattices(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_84]),c_0_40]),c_0_28]),c_0_29])]),c_0_30]),c_0_114])).

cnf(c_0_128,negated_conjecture,
    ( k4_lattices(esk4_0,k6_lattices(esk4_0),k6_lattices(esk4_0)) = k6_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_84]),c_0_71]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_129,negated_conjecture,
    ( k4_lattices(esk4_0,X1,X2) = k4_lattices(esk4_0,X2,X1)
    | ~ l1_lattices(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_130,negated_conjecture,
    ( k4_lattices(esk4_0,k7_lattices(esk4_0,k4_lattices(esk4_0,X1,k5_lattices(esk4_0))),k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k7_lattices(esk4_0,esk6_0))) = k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k7_lattices(esk4_0,esk6_0))
    | ~ m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_119]),c_0_84])])).

cnf(c_0_131,negated_conjecture,
    ( k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k7_lattices(esk4_0,X1)) = k7_lattices(esk4_0,k4_lattices(esk4_0,X1,esk5_0))
    | ~ m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ l2_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_65]),c_0_67]),c_0_54])]),c_0_30])).

cnf(c_0_132,negated_conjecture,
    ( k4_lattices(esk4_0,esk5_0,k5_lattices(esk4_0)) = k5_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_50]),c_0_122]),c_0_28]),c_0_29]),c_0_89])]),c_0_30])).

cnf(c_0_133,negated_conjecture,
    ( k4_lattices(esk4_0,esk6_0,esk5_0) = k4_lattices(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_45]),c_0_29])])).

cnf(c_0_134,negated_conjecture,
    ( k4_lattices(esk4_0,k6_lattices(esk4_0),k7_lattices(esk4_0,k4_lattices(esk4_0,esk5_0,esk6_0))) = k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k4_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_52]),c_0_53]),c_0_50])])).

cnf(c_0_135,negated_conjecture,
    ( k4_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0)) = esk5_0
    | k5_lattices(esk4_0) = k4_lattices(esk4_0,esk5_0,esk6_0)
    | ~ l1_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_53]),c_0_50]),c_0_35])]),c_0_30])).

cnf(c_0_136,negated_conjecture,
    ( k3_lattices(esk4_0,k5_lattices(esk4_0),k5_lattices(esk4_0)) = k5_lattices(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_114]),c_0_114]),c_0_84])])).

cnf(c_0_137,negated_conjecture,
    ( k4_lattices(esk4_0,X1,X2) = k4_lattices(esk4_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_45]),c_0_29])])).

cnf(c_0_138,negated_conjecture,
    ( k4_lattices(esk4_0,esk6_0,k6_lattices(esk4_0)) = esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_57]),c_0_34]),c_0_71]),c_0_28]),c_0_29]),c_0_84])]),c_0_30])).

cnf(c_0_139,negated_conjecture,
    ( k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k4_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0))) = k7_lattices(esk4_0,k4_lattices(esk4_0,esk5_0,esk6_0))
    | ~ l2_lattices(esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_132]),c_0_101]),c_0_67]),c_0_50]),c_0_53]),c_0_34])]),c_0_133]),c_0_134]),c_0_133])).

cnf(c_0_140,negated_conjecture,
    ( k4_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0)) = esk5_0
    | k5_lattices(esk4_0) = k4_lattices(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_45]),c_0_29])])).

cnf(c_0_141,negated_conjecture,
    ( k7_lattices(esk4_0,k7_lattices(esk4_0,esk6_0)) = esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_34]),c_0_40]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_142,negated_conjecture,
    ( k3_lattices(esk4_0,k5_lattices(esk4_0),k4_lattices(esk4_0,X1,k5_lattices(esk4_0))) = k4_lattices(esk4_0,k3_lattices(esk4_0,k5_lattices(esk4_0),X1),k5_lattices(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_136]),c_0_89]),c_0_105]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_143,negated_conjecture,
    ( k4_lattices(esk4_0,X1,k5_lattices(esk4_0)) = k5_lattices(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_137]),c_0_122]),c_0_28]),c_0_29]),c_0_89])]),c_0_30])).

cnf(c_0_144,negated_conjecture,
    ( k4_lattices(esk4_0,k6_lattices(esk4_0),esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_50]),c_0_28]),c_0_29])]),c_0_30]),c_0_71])])).

cnf(c_0_145,negated_conjecture,
    ( k4_lattices(esk4_0,k3_lattices(esk4_0,X1,X2),k3_lattices(esk4_0,X1,k5_lattices(esk4_0))) = k3_lattices(esk4_0,X1,k4_lattices(esk4_0,X2,k5_lattices(esk4_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_89]),c_0_105]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_146,negated_conjecture,
    ( k3_lattices(esk4_0,k7_lattices(esk4_0,esk6_0),k5_lattices(esk4_0)) = k7_lattices(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_138]),c_0_34])])).

cnf(c_0_147,negated_conjecture,
    ( k4_lattices(esk4_0,k5_lattices(esk4_0),k5_lattices(esk4_0)) = k5_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_89]),c_0_122]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_148,negated_conjecture,
    ( k7_lattices(esk4_0,k4_lattices(esk4_0,esk5_0,esk6_0)) = k6_lattices(esk4_0)
    | k5_lattices(esk4_0) = k4_lattices(esk4_0,esk5_0,esk6_0)
    | ~ l2_lattices(esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_110])).

cnf(c_0_149,negated_conjecture,
    ( k7_lattices(esk4_0,k4_lattices(esk4_0,k7_lattices(esk4_0,esk6_0),X1)) = k3_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_141]),c_0_53]),c_0_40]),c_0_28]),c_0_29])]),c_0_30])).

fof(c_0_150,plain,(
    ! [X34,X35,X36] :
      ( v2_struct_0(X34)
      | ~ v4_lattices(X34)
      | ~ l2_lattices(X34)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | ~ m1_subset_1(X36,u1_struct_0(X34))
      | k3_lattices(X34,X35,X36) = k1_lattices(X34,X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

cnf(c_0_151,negated_conjecture,
    ( k4_lattices(esk4_0,k3_lattices(esk4_0,k5_lattices(esk4_0),X1),k5_lattices(esk4_0)) = k5_lattices(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_136])).

cnf(c_0_152,negated_conjecture,
    ( k3_lattices(esk4_0,k5_lattices(esk4_0),k7_lattices(esk4_0,esk5_0)) = k7_lattices(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_114]),c_0_144]),c_0_84])])).

cnf(c_0_153,negated_conjecture,
    ( k7_lattices(esk4_0,k4_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))) = k3_lattices(esk4_0,k7_lattices(esk4_0,X1),esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_53]),c_0_40]),c_0_28]),c_0_29])]),c_0_30]),c_0_141])).

cnf(c_0_154,negated_conjecture,
    ( k4_lattices(esk4_0,k7_lattices(esk4_0,esk6_0),k7_lattices(esk4_0,esk6_0)) = k7_lattices(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_146]),c_0_146]),c_0_147]),c_0_146]),c_0_89]),c_0_53])])).

cnf(c_0_155,negated_conjecture,
    ( k7_lattices(esk4_0,k4_lattices(esk4_0,esk5_0,esk6_0)) = k6_lattices(esk4_0)
    | k5_lattices(esk4_0) = k4_lattices(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_61]),c_0_29])])).

cnf(c_0_156,negated_conjecture,
    ( k4_lattices(esk4_0,k3_lattices(esk4_0,X1,X2),k3_lattices(esk4_0,X1,esk6_0)) = k3_lattices(esk4_0,X1,k4_lattices(esk4_0,X2,esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_34]),c_0_28]),c_0_29])]),c_0_30]),c_0_105])])).

cnf(c_0_157,negated_conjecture,
    ( k4_lattices(esk4_0,k6_lattices(esk4_0),esk6_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_34]),c_0_28]),c_0_29])]),c_0_30]),c_0_71])])).

cnf(c_0_158,negated_conjecture,
    ( k7_lattices(esk4_0,k4_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0))) = k3_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_121]),c_0_50]),c_0_53])])).

cnf(c_0_159,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

fof(c_0_160,plain,(
    ! [X21,X22,X23] :
      ( ( ~ v9_lattices(X21)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | k2_lattices(X21,X22,k1_lattices(X21,X22,X23)) = X22
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( m1_subset_1(esk2_1(X21),u1_struct_0(X21))
        | v9_lattices(X21)
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( m1_subset_1(esk3_1(X21),u1_struct_0(X21))
        | v9_lattices(X21)
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( k2_lattices(X21,esk2_1(X21),k1_lattices(X21,esk2_1(X21),esk3_1(X21))) != esk2_1(X21)
        | v9_lattices(X21)
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).

cnf(c_0_161,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_150])).

cnf(c_0_162,negated_conjecture,
    ( k4_lattices(esk4_0,k7_lattices(esk4_0,k4_lattices(esk4_0,X1,esk5_0)),k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k5_lattices(esk4_0))) = k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k4_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k5_lattices(esk4_0)))
    | ~ m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_65]),c_0_67])])).

cnf(c_0_163,negated_conjecture,
    ( k4_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k5_lattices(esk4_0)) = k5_lattices(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_152]),c_0_67])])).

cnf(c_0_164,negated_conjecture,
    ( k3_lattices(esk4_0,esk6_0,esk6_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_154]),c_0_141]),c_0_141]),c_0_53])])).

cnf(c_0_165,negated_conjecture,
    ( k3_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk6_0)) = k6_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_141]),c_0_53]),c_0_40]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_166,negated_conjecture,
    ( k4_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk6_0)) = k5_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_141]),c_0_53]),c_0_40]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_167,negated_conjecture,
    ( k4_lattices(esk4_0,esk5_0,k6_lattices(esk4_0)) = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_121]),c_0_50]),c_0_71]),c_0_28]),c_0_29]),c_0_84])]),c_0_30])).

cnf(c_0_168,negated_conjecture,
    ( k5_lattices(esk4_0) = k4_lattices(esk4_0,esk5_0,esk6_0)
    | ~ l1_lattices(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_155]),c_0_114]),c_0_50])])).

cnf(c_0_169,negated_conjecture,
    ( k4_lattices(esk4_0,k7_lattices(esk4_0,k4_lattices(esk4_0,X1,k5_lattices(esk4_0))),k3_lattices(esk4_0,k7_lattices(esk4_0,X1),esk6_0)) = k3_lattices(esk4_0,k7_lattices(esk4_0,X1),esk6_0)
    | ~ m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_118]),c_0_157]),c_0_84])])).

cnf(c_0_170,negated_conjecture,
    ( k4_lattices(esk4_0,k6_lattices(esk4_0),k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),esk6_0)) = k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k4_lattices(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_110]),c_0_50]),c_0_67])])).

cnf(c_0_171,negated_conjecture,
    ( k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),esk6_0) = k3_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_158]),c_0_50])])).

cnf(c_0_172,negated_conjecture,
    ( k4_lattices(esk4_0,k7_lattices(esk4_0,k4_lattices(esk4_0,X1,esk5_0)),k3_lattices(esk4_0,k7_lattices(esk4_0,X1),X2)) = k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k4_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),X2))
    | ~ m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_65]),c_0_67]),c_0_105]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_173,negated_conjecture,
    ( k4_lattices(esk4_0,k3_lattices(esk4_0,X1,X2),k3_lattices(esk4_0,X1,k7_lattices(esk4_0,esk5_0))) = k3_lattices(esk4_0,X1,k4_lattices(esk4_0,X2,k7_lattices(esk4_0,esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_67]),c_0_105]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_174,negated_conjecture,
    ( k3_lattices(esk4_0,k5_lattices(esk4_0),esk6_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_119]),c_0_141]),c_0_114]),c_0_84])])).

cnf(c_0_175,negated_conjecture,
    ( k4_lattices(esk4_0,esk5_0,esk6_0) != k5_lattices(esk4_0)
    | ~ r3_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_176,negated_conjecture,
    ( r3_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))
    | ~ r1_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_53]),c_0_87]),c_0_88]),c_0_35]),c_0_29])]),c_0_30])).

cnf(c_0_177,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X3) != X2
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_178,plain,
    ( k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_160])).

cnf(c_0_179,negated_conjecture,
    ( k1_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0)) = k3_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ l2_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_53]),c_0_54])]),c_0_30])).

cnf(c_0_180,negated_conjecture,
    ( k3_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0)) = k3_lattices(esk4_0,k7_lattices(esk4_0,esk6_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ l2_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_53]),c_0_54])]),c_0_30])).

cnf(c_0_181,negated_conjecture,
    ( k4_lattices(esk4_0,k7_lattices(esk4_0,k4_lattices(esk4_0,X1,esk5_0)),k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k5_lattices(esk4_0))) = k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k5_lattices(esk4_0))
    | ~ m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_162,c_0_163])).

cnf(c_0_182,negated_conjecture,
    ( k7_lattices(esk4_0,k4_lattices(esk4_0,k7_lattices(esk4_0,esk6_0),esk5_0)) = k3_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_141]),c_0_53])])).

cnf(c_0_183,negated_conjecture,
    ( k3_lattices(esk4_0,esk6_0,k5_lattices(esk4_0)) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_164]),c_0_165]),c_0_138]),c_0_166]),c_0_34])])).

cnf(c_0_184,negated_conjecture,
    ( k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k5_lattices(esk4_0)) = k7_lattices(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_167]),c_0_50])])).

cnf(c_0_185,negated_conjecture,
    ( k5_lattices(esk4_0) = k4_lattices(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_45]),c_0_29])])).

cnf(c_0_186,negated_conjecture,
    ( k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k4_lattices(esk4_0,esk5_0,esk6_0)) = k3_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_132]),c_0_101]),c_0_170]),c_0_67]),c_0_50])]),c_0_171])).

cnf(c_0_187,negated_conjecture,
    ( k3_lattices(esk4_0,k5_lattices(esk4_0),k4_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),X1)) = k4_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k3_lattices(esk4_0,k5_lattices(esk4_0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172,c_0_114]),c_0_144]),c_0_89]),c_0_84])])).

cnf(c_0_188,negated_conjecture,
    ( k3_lattices(esk4_0,k5_lattices(esk4_0),k4_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0))) = k4_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_174]),c_0_34]),c_0_89])]),c_0_152])).

cnf(c_0_189,negated_conjecture,
    ( k5_lattices(esk4_0) != k4_lattices(esk4_0,esk5_0,esk6_0)
    | ~ r1_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_176]),c_0_50])])).

cnf(c_0_190,negated_conjecture,
    ( r1_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))
    | k2_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0)) != X1
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_53]),c_0_87]),c_0_88]),c_0_29])]),c_0_30])).

cnf(c_0_191,negated_conjecture,
    ( k2_lattices(esk4_0,X1,k3_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ l2_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_179]),c_0_53]),c_0_87]),c_0_29])]),c_0_30])).

cnf(c_0_192,negated_conjecture,
    ( k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k7_lattices(esk4_0,esk6_0)) = k7_lattices(esk4_0,k4_lattices(esk4_0,esk6_0,X1))
    | ~ m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ l2_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_180]),c_0_34]),c_0_40]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_193,negated_conjecture,
    ( k4_lattices(esk4_0,k3_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0)),esk6_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_141]),c_0_182]),c_0_183]),c_0_183]),c_0_34]),c_0_53])])).

cnf(c_0_194,negated_conjecture,
    ( k3_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0)) = k7_lattices(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_184,c_0_185]),c_0_186])).

cnf(c_0_195,negated_conjecture,
    ( k4_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),esk6_0) = k4_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187,c_0_57]),c_0_188]),c_0_174]),c_0_34]),c_0_67])])).

cnf(c_0_196,negated_conjecture,
    ( k2_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0)) != esk5_0
    | k5_lattices(esk4_0) != k4_lattices(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189,c_0_190]),c_0_50])])).

cnf(c_0_197,negated_conjecture,
    ( k2_lattices(esk4_0,k7_lattices(esk4_0,X1),k7_lattices(esk4_0,k4_lattices(esk4_0,esk6_0,X1))) = k7_lattices(esk4_0,X1)
    | ~ m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ l2_lattices(esk4_0) ),
    inference(spm,[status(thm)],[c_0_191,c_0_192])).

cnf(c_0_198,negated_conjecture,
    ( k4_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0)) = esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_193,c_0_194]),c_0_195])).

cnf(c_0_199,negated_conjecture,
    ( k7_lattices(esk4_0,k7_lattices(esk4_0,esk5_0)) = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_50]),c_0_40]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_200,negated_conjecture,
    ( k2_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0)) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_196,c_0_185])])).

cnf(c_0_201,negated_conjecture,
    ( ~ l2_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197,c_0_198]),c_0_199]),c_0_199]),c_0_199]),c_0_50]),c_0_67])]),c_0_200])).

cnf(c_0_202,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201,c_0_61]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 49.95/50.14  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 49.95/50.14  # and selection function PSelectComplexExceptUniqMaxHorn.
% 49.95/50.14  #
% 49.95/50.14  # Preprocessing time       : 0.031 s
% 49.95/50.14  
% 49.95/50.14  # Proof found!
% 49.95/50.14  # SZS status Theorem
% 49.95/50.14  # SZS output start CNFRefutation
% 49.95/50.14  fof(t52_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k4_lattices(X1,X2,X3)=k5_lattices(X1)<=>r3_lattices(X1,X2,k7_lattices(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_lattices)).
% 49.95/50.14  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 49.95/50.14  fof(commutativity_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 49.95/50.14  fof(t50_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k7_lattices(X1,k4_lattices(X1,X2,X3))=k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattices)).
% 49.95/50.14  fof(dt_k7_lattices, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_lattices)).
% 49.95/50.14  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 49.95/50.14  fof(cc5_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v17_lattices(X1))=>(((~(v2_struct_0(X1))&v11_lattices(X1))&v15_lattices(X1))&v16_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_lattices)).
% 49.95/50.15  fof(commutativity_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 49.95/50.15  fof(dt_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_lattices)).
% 49.95/50.15  fof(cc4_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v15_lattices(X1))=>((~(v2_struct_0(X1))&v13_lattices(X1))&v14_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_lattices)).
% 49.95/50.15  fof(dt_k6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>m1_subset_1(k6_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_lattices)).
% 49.95/50.15  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 49.95/50.15  fof(t43_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v14_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,k6_lattices(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_lattices)).
% 49.95/50.15  fof(t47_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,k7_lattices(X1,X2),X2)=k5_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_lattices)).
% 49.95/50.15  fof(t49_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k7_lattices(X1,k7_lattices(X1,X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_lattices)).
% 49.95/50.15  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 49.95/50.15  fof(t48_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k3_lattices(X1,k7_lattices(X1,X2),X2)=k6_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattices)).
% 49.95/50.15  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 49.95/50.15  fof(t31_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>k3_lattices(X1,X2,k4_lattices(X1,X3,X4))=k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_lattices)).
% 49.95/50.15  fof(t40_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,k5_lattices(X1),X2)=k5_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_lattices)).
% 49.95/50.15  fof(redefinition_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 49.95/50.15  fof(redefinition_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 49.95/50.15  fof(d9_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v9_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattices)).
% 49.95/50.15  fof(c_0_23, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k4_lattices(X1,X2,X3)=k5_lattices(X1)<=>r3_lattices(X1,X2,k7_lattices(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_lattices])).
% 49.95/50.15  fof(c_0_24, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 49.95/50.15  fof(c_0_25, negated_conjecture, ((((~v2_struct_0(esk4_0)&v10_lattices(esk4_0))&v17_lattices(esk4_0))&l3_lattices(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&((k4_lattices(esk4_0,esk5_0,esk6_0)!=k5_lattices(esk4_0)|~r3_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0)))&(k4_lattices(esk4_0,esk5_0,esk6_0)=k5_lattices(esk4_0)|r3_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).
% 49.95/50.15  fof(c_0_26, plain, ![X11, X12, X13]:(v2_struct_0(X11)|~v6_lattices(X11)|~l1_lattices(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~m1_subset_1(X13,u1_struct_0(X11))|k4_lattices(X11,X12,X13)=k4_lattices(X11,X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).
% 49.95/50.15  cnf(c_0_27, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 49.95/50.15  cnf(c_0_28, negated_conjecture, (v10_lattices(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 49.95/50.15  cnf(c_0_29, negated_conjecture, (l3_lattices(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 49.95/50.15  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 49.95/50.15  fof(c_0_31, plain, ![X64, X65, X66]:(v2_struct_0(X64)|~v10_lattices(X64)|~v17_lattices(X64)|~l3_lattices(X64)|(~m1_subset_1(X65,u1_struct_0(X64))|(~m1_subset_1(X66,u1_struct_0(X64))|k7_lattices(X64,k4_lattices(X64,X65,X66))=k3_lattices(X64,k7_lattices(X64,X65),k7_lattices(X64,X66))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_lattices])])])])).
% 49.95/50.15  fof(c_0_32, plain, ![X31, X32]:(v2_struct_0(X31)|~l3_lattices(X31)|~m1_subset_1(X32,u1_struct_0(X31))|m1_subset_1(k7_lattices(X31,X32),u1_struct_0(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).
% 49.95/50.15  cnf(c_0_33, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 49.95/50.15  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 49.95/50.15  cnf(c_0_35, negated_conjecture, (v6_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  fof(c_0_36, plain, ![X33]:((l1_lattices(X33)|~l3_lattices(X33))&(l2_lattices(X33)|~l3_lattices(X33))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 49.95/50.15  fof(c_0_37, plain, ![X7]:((((~v2_struct_0(X7)|(v2_struct_0(X7)|~v17_lattices(X7))|~l3_lattices(X7))&(v11_lattices(X7)|(v2_struct_0(X7)|~v17_lattices(X7))|~l3_lattices(X7)))&(v15_lattices(X7)|(v2_struct_0(X7)|~v17_lattices(X7))|~l3_lattices(X7)))&(v16_lattices(X7)|(v2_struct_0(X7)|~v17_lattices(X7))|~l3_lattices(X7))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_lattices])])])])).
% 49.95/50.15  fof(c_0_38, plain, ![X8, X9, X10]:(v2_struct_0(X8)|~v4_lattices(X8)|~l2_lattices(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~m1_subset_1(X10,u1_struct_0(X8))|k3_lattices(X8,X9,X10)=k3_lattices(X8,X10,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).
% 49.95/50.15  cnf(c_0_39, plain, (v2_struct_0(X1)|k7_lattices(X1,k4_lattices(X1,X2,X3))=k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 49.95/50.15  cnf(c_0_40, negated_conjecture, (v17_lattices(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 49.95/50.15  cnf(c_0_41, plain, (v2_struct_0(X1)|m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 49.95/50.15  cnf(c_0_42, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 49.95/50.15  fof(c_0_43, plain, ![X26, X27, X28]:(v2_struct_0(X26)|~v6_lattices(X26)|~l1_lattices(X26)|~m1_subset_1(X27,u1_struct_0(X26))|~m1_subset_1(X28,u1_struct_0(X26))|m1_subset_1(k4_lattices(X26,X27,X28),u1_struct_0(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).
% 49.95/50.15  cnf(c_0_44, negated_conjecture, (k4_lattices(esk4_0,X1,esk6_0)=k4_lattices(esk4_0,esk6_0,X1)|~l1_lattices(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_30]), c_0_35])])).
% 49.95/50.15  cnf(c_0_45, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 49.95/50.15  fof(c_0_46, plain, ![X6]:(((~v2_struct_0(X6)|(v2_struct_0(X6)|~v15_lattices(X6))|~l3_lattices(X6))&(v13_lattices(X6)|(v2_struct_0(X6)|~v15_lattices(X6))|~l3_lattices(X6)))&(v14_lattices(X6)|(v2_struct_0(X6)|~v15_lattices(X6))|~l3_lattices(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_lattices])])])])).
% 49.95/50.15  cnf(c_0_47, plain, (v15_lattices(X1)|v2_struct_0(X1)|~v17_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 49.95/50.15  fof(c_0_48, plain, ![X30]:(v2_struct_0(X30)|~l2_lattices(X30)|m1_subset_1(k6_lattices(X30),u1_struct_0(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_lattices])])])).
% 49.95/50.15  fof(c_0_49, plain, ![X29]:(v2_struct_0(X29)|~l1_lattices(X29)|m1_subset_1(k5_lattices(X29),u1_struct_0(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 49.95/50.15  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 49.95/50.15  cnf(c_0_51, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 49.95/50.15  cnf(c_0_52, negated_conjecture, (k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k7_lattices(esk4_0,esk6_0))=k7_lattices(esk4_0,k4_lattices(esk4_0,X1,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_34]), c_0_40]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_53, negated_conjecture, (m1_subset_1(k7_lattices(esk4_0,esk6_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_34]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_54, negated_conjecture, (v4_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_55, plain, (v2_struct_0(X1)|m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 49.95/50.15  fof(c_0_56, plain, ![X56, X57]:(v2_struct_0(X56)|~v10_lattices(X56)|~v14_lattices(X56)|~l3_lattices(X56)|(~m1_subset_1(X57,u1_struct_0(X56))|k4_lattices(X56,k6_lattices(X56),X57)=X57)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_lattices])])])])).
% 49.95/50.15  cnf(c_0_57, negated_conjecture, (k4_lattices(esk4_0,X1,esk6_0)=k4_lattices(esk4_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_29])])).
% 49.95/50.15  cnf(c_0_58, plain, (v14_lattices(X1)|v2_struct_0(X1)|~v15_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 49.95/50.15  cnf(c_0_59, negated_conjecture, (v15_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_40]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_60, plain, (v2_struct_0(X1)|m1_subset_1(k6_lattices(X1),u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 49.95/50.15  cnf(c_0_61, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 49.95/50.15  cnf(c_0_62, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 49.95/50.15  fof(c_0_63, plain, ![X58, X59]:(v2_struct_0(X58)|~v10_lattices(X58)|~v17_lattices(X58)|~l3_lattices(X58)|(~m1_subset_1(X59,u1_struct_0(X58))|k4_lattices(X58,k7_lattices(X58,X59),X59)=k5_lattices(X58))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattices])])])])).
% 49.95/50.15  fof(c_0_64, plain, ![X62, X63]:(v2_struct_0(X62)|~v10_lattices(X62)|~v17_lattices(X62)|~l3_lattices(X62)|(~m1_subset_1(X63,u1_struct_0(X62))|k7_lattices(X62,k7_lattices(X62,X63))=X63)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_lattices])])])])).
% 49.95/50.15  cnf(c_0_65, negated_conjecture, (k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k7_lattices(esk4_0,esk5_0))=k7_lattices(esk4_0,k4_lattices(esk4_0,X1,esk5_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_50]), c_0_40]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_66, negated_conjecture, (k3_lattices(esk4_0,k7_lattices(esk4_0,esk6_0),k7_lattices(esk4_0,X1))=k7_lattices(esk4_0,k4_lattices(esk4_0,X1,esk6_0))|~m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))|~l2_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54])]), c_0_30])).
% 49.95/50.15  cnf(c_0_67, negated_conjecture, (m1_subset_1(k7_lattices(esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_50]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_68, negated_conjecture, (m1_subset_1(k4_lattices(esk4_0,X1,esk5_0),u1_struct_0(esk4_0))|~l1_lattices(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_50]), c_0_30]), c_0_35])])).
% 49.95/50.15  cnf(c_0_69, plain, (v2_struct_0(X1)|k4_lattices(X1,k6_lattices(X1),X2)=X2|~v10_lattices(X1)|~v14_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 49.95/50.15  cnf(c_0_70, negated_conjecture, (m1_subset_1(k4_lattices(esk4_0,esk6_0,X1),u1_struct_0(esk4_0))|~l1_lattices(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_57]), c_0_34]), c_0_35])]), c_0_30])).
% 49.95/50.15  cnf(c_0_71, negated_conjecture, (v14_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_72, plain, (m1_subset_1(k6_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 49.95/50.15  fof(c_0_73, plain, ![X40, X41, X42]:((~r3_lattices(X40,X41,X42)|r1_lattices(X40,X41,X42)|(v2_struct_0(X40)|~v6_lattices(X40)|~v8_lattices(X40)|~v9_lattices(X40)|~l3_lattices(X40)|~m1_subset_1(X41,u1_struct_0(X40))|~m1_subset_1(X42,u1_struct_0(X40))))&(~r1_lattices(X40,X41,X42)|r3_lattices(X40,X41,X42)|(v2_struct_0(X40)|~v6_lattices(X40)|~v8_lattices(X40)|~v9_lattices(X40)|~l3_lattices(X40)|~m1_subset_1(X41,u1_struct_0(X40))|~m1_subset_1(X42,u1_struct_0(X40))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 49.95/50.15  cnf(c_0_74, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 49.95/50.15  cnf(c_0_75, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 49.95/50.15  cnf(c_0_76, plain, (m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_62, c_0_45])).
% 49.95/50.15  fof(c_0_77, plain, ![X60, X61]:(v2_struct_0(X60)|~v10_lattices(X60)|~v17_lattices(X60)|~l3_lattices(X60)|(~m1_subset_1(X61,u1_struct_0(X60))|k3_lattices(X60,k7_lattices(X60,X61),X61)=k6_lattices(X60))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattices])])])])).
% 49.95/50.15  cnf(c_0_78, plain, (v2_struct_0(X1)|k4_lattices(X1,k7_lattices(X1,X2),X2)=k5_lattices(X1)|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 49.95/50.15  cnf(c_0_79, plain, (v2_struct_0(X1)|k7_lattices(X1,k7_lattices(X1,X2))=X2|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 49.95/50.15  cnf(c_0_80, negated_conjecture, (m1_subset_1(k4_lattices(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))|~l1_lattices(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_34]), c_0_30]), c_0_35])])).
% 49.95/50.15  cnf(c_0_81, negated_conjecture, (k7_lattices(esk4_0,k4_lattices(esk4_0,esk6_0,esk5_0))=k7_lattices(esk4_0,k4_lattices(esk4_0,esk5_0,esk6_0))|~l2_lattices(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_34]), c_0_67]), c_0_50])])).
% 49.95/50.15  cnf(c_0_82, negated_conjecture, (m1_subset_1(k4_lattices(esk4_0,X1,k4_lattices(esk4_0,X2,esk5_0)),u1_struct_0(esk4_0))|~l1_lattices(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~m1_subset_1(X2,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_68]), c_0_35])]), c_0_30])).
% 49.95/50.15  cnf(c_0_83, negated_conjecture, (k4_lattices(esk4_0,k6_lattices(esk4_0),k4_lattices(esk4_0,esk6_0,X1))=k4_lattices(esk4_0,esk6_0,X1)|~l1_lattices(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_84, negated_conjecture, (m1_subset_1(k6_lattices(esk4_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_29]), c_0_30])).
% 49.95/50.15  fof(c_0_85, plain, ![X43, X44, X45]:((~r1_lattices(X43,X44,X45)|k2_lattices(X43,X44,X45)=X44|~m1_subset_1(X45,u1_struct_0(X43))|~m1_subset_1(X44,u1_struct_0(X43))|(v2_struct_0(X43)|~v8_lattices(X43)|~v9_lattices(X43)|~l3_lattices(X43)))&(k2_lattices(X43,X44,X45)!=X44|r1_lattices(X43,X44,X45)|~m1_subset_1(X45,u1_struct_0(X43))|~m1_subset_1(X44,u1_struct_0(X43))|(v2_struct_0(X43)|~v8_lattices(X43)|~v9_lattices(X43)|~l3_lattices(X43)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 49.95/50.15  cnf(c_0_86, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 49.95/50.15  cnf(c_0_87, negated_conjecture, (v9_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_88, negated_conjecture, (v8_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_89, negated_conjecture, (m1_subset_1(k5_lattices(esk4_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_29]), c_0_30])).
% 49.95/50.15  cnf(c_0_90, plain, (v2_struct_0(X1)|k3_lattices(X1,k7_lattices(X1,X2),X2)=k6_lattices(X1)|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 49.95/50.15  cnf(c_0_91, negated_conjecture, (k4_lattices(esk4_0,k7_lattices(esk4_0,esk6_0),esk6_0)=k5_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_34]), c_0_40]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  fof(c_0_92, plain, ![X50, X51, X52, X53]:(v2_struct_0(X50)|~v10_lattices(X50)|~v11_lattices(X50)|~l3_lattices(X50)|(~m1_subset_1(X51,u1_struct_0(X50))|(~m1_subset_1(X52,u1_struct_0(X50))|(~m1_subset_1(X53,u1_struct_0(X50))|k3_lattices(X50,X51,k4_lattices(X50,X52,X53))=k4_lattices(X50,k3_lattices(X50,X51,X52),k3_lattices(X50,X51,X53)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_lattices])])])])).
% 49.95/50.15  cnf(c_0_93, plain, (v11_lattices(X1)|v2_struct_0(X1)|~v17_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 49.95/50.15  cnf(c_0_94, negated_conjecture, (k7_lattices(esk4_0,k7_lattices(esk4_0,k4_lattices(esk4_0,X1,esk6_0)))=k4_lattices(esk4_0,X1,esk6_0)|~l1_lattices(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_40]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_95, negated_conjecture, (k7_lattices(esk4_0,k7_lattices(esk4_0,k4_lattices(esk4_0,esk5_0,esk6_0)))=k4_lattices(esk4_0,esk6_0,esk5_0)|~m1_subset_1(k4_lattices(esk4_0,esk6_0,esk5_0),u1_struct_0(esk4_0))|~l2_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_81]), c_0_40]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_96, negated_conjecture, (m1_subset_1(k4_lattices(esk4_0,esk6_0,esk5_0),u1_struct_0(esk4_0))|~l1_lattices(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_34]), c_0_50])])).
% 49.95/50.15  cnf(c_0_97, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 49.95/50.15  cnf(c_0_98, negated_conjecture, (r1_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))|~r3_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_53]), c_0_87]), c_0_88]), c_0_35]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_99, negated_conjecture, (k4_lattices(esk4_0,esk5_0,esk6_0)=k5_lattices(esk4_0)|r3_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 49.95/50.15  cnf(c_0_100, negated_conjecture, (k7_lattices(esk4_0,k7_lattices(esk4_0,k5_lattices(esk4_0)))=k5_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_89]), c_0_40]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_101, negated_conjecture, (k7_lattices(esk4_0,k5_lattices(esk4_0))=k6_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_52]), c_0_91]), c_0_53]), c_0_40]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_102, negated_conjecture, (m1_subset_1(k4_lattices(esk4_0,X1,k6_lattices(esk4_0)),u1_struct_0(esk4_0))|~l1_lattices(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_84]), c_0_35])]), c_0_30])).
% 49.95/50.15  cnf(c_0_103, negated_conjecture, (k4_lattices(esk4_0,X1,k6_lattices(esk4_0))=k4_lattices(esk4_0,k6_lattices(esk4_0),X1)|~l1_lattices(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_84]), c_0_35])]), c_0_30])).
% 49.95/50.15  cnf(c_0_104, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,k4_lattices(X1,X3,X4))=k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X2,X4))|~v10_lattices(X1)|~v11_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_92])).
% 49.95/50.15  cnf(c_0_105, negated_conjecture, (v11_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_40]), c_0_29])]), c_0_30])).
% 49.95/50.15  fof(c_0_106, plain, ![X54, X55]:(v2_struct_0(X54)|~v10_lattices(X54)|~v13_lattices(X54)|~l3_lattices(X54)|(~m1_subset_1(X55,u1_struct_0(X54))|k4_lattices(X54,k5_lattices(X54),X55)=k5_lattices(X54))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_lattices])])])])).
% 49.95/50.15  cnf(c_0_107, negated_conjecture, (k4_lattices(esk4_0,X1,esk5_0)=k4_lattices(esk4_0,esk5_0,X1)|~l1_lattices(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_50]), c_0_30]), c_0_35])])).
% 49.95/50.15  cnf(c_0_108, plain, (v13_lattices(X1)|v2_struct_0(X1)|~v15_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 49.95/50.15  cnf(c_0_109, negated_conjecture, (k4_lattices(esk4_0,esk6_0,esk5_0)=k4_lattices(esk4_0,esk5_0,esk6_0)|~l1_lattices(esk4_0)|~l2_lattices(esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_50])]), c_0_96])).
% 49.95/50.15  cnf(c_0_110, negated_conjecture, (k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),esk5_0)=k6_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_50]), c_0_40]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  fof(c_0_111, plain, ![X37, X38, X39]:(v2_struct_0(X37)|~v6_lattices(X37)|~l1_lattices(X37)|~m1_subset_1(X38,u1_struct_0(X37))|~m1_subset_1(X39,u1_struct_0(X37))|k4_lattices(X37,X38,X39)=k2_lattices(X37,X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).
% 49.95/50.15  cnf(c_0_112, negated_conjecture, (k2_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))=X1|~r1_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_53]), c_0_87]), c_0_88]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_113, negated_conjecture, (k5_lattices(esk4_0)=k4_lattices(esk4_0,esk5_0,esk6_0)|r1_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_50])])).
% 49.95/50.15  cnf(c_0_114, negated_conjecture, (k7_lattices(esk4_0,k6_lattices(esk4_0))=k5_lattices(esk4_0)), inference(rw,[status(thm)],[c_0_100, c_0_101])).
% 49.95/50.15  cnf(c_0_115, negated_conjecture, (k4_lattices(esk4_0,X1,k4_lattices(esk4_0,X2,k6_lattices(esk4_0)))=k4_lattices(esk4_0,k4_lattices(esk4_0,X2,k6_lattices(esk4_0)),X1)|~l1_lattices(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~m1_subset_1(X2,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_102]), c_0_35])]), c_0_30])).
% 49.95/50.15  cnf(c_0_116, negated_conjecture, (k4_lattices(esk4_0,X1,k6_lattices(esk4_0))=X1|~l1_lattices(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_103]), c_0_71]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_117, negated_conjecture, (k4_lattices(esk4_0,k3_lattices(esk4_0,X1,X2),k3_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0)))=k3_lattices(esk4_0,X1,k4_lattices(esk4_0,X2,k7_lattices(esk4_0,esk6_0)))|~m1_subset_1(X2,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_53]), c_0_105]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_118, negated_conjecture, (k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k6_lattices(esk4_0))=k7_lattices(esk4_0,k4_lattices(esk4_0,X1,k5_lattices(esk4_0)))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_89]), c_0_40]), c_0_28]), c_0_29])]), c_0_30]), c_0_101])).
% 49.95/50.15  cnf(c_0_119, negated_conjecture, (k4_lattices(esk4_0,k6_lattices(esk4_0),k7_lattices(esk4_0,esk6_0))=k7_lattices(esk4_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_53]), c_0_71]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_120, plain, (v2_struct_0(X1)|k4_lattices(X1,k5_lattices(X1),X2)=k5_lattices(X1)|~v10_lattices(X1)|~v13_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_106])).
% 49.95/50.15  cnf(c_0_121, negated_conjecture, (k4_lattices(esk4_0,X1,esk5_0)=k4_lattices(esk4_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_45]), c_0_29])])).
% 49.95/50.15  cnf(c_0_122, negated_conjecture, (v13_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_59]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_123, negated_conjecture, (k4_lattices(esk4_0,esk6_0,esk5_0)=k4_lattices(esk4_0,esk5_0,esk6_0)|~l1_lattices(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_61]), c_0_29])])).
% 49.95/50.15  cnf(c_0_124, negated_conjecture, (k4_lattices(esk4_0,k6_lattices(esk4_0),k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),X1))=k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k4_lattices(esk4_0,esk5_0,X1))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_110]), c_0_50]), c_0_67]), c_0_105]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_125, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_111])).
% 49.95/50.15  cnf(c_0_126, negated_conjecture, (k2_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0))=esk5_0|k5_lattices(esk4_0)=k4_lattices(esk4_0,esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_50])])).
% 49.95/50.15  cnf(c_0_127, negated_conjecture, (k7_lattices(esk4_0,k4_lattices(esk4_0,X1,k6_lattices(esk4_0)))=k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k5_lattices(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_84]), c_0_40]), c_0_28]), c_0_29])]), c_0_30]), c_0_114])).
% 49.95/50.15  cnf(c_0_128, negated_conjecture, (k4_lattices(esk4_0,k6_lattices(esk4_0),k6_lattices(esk4_0))=k6_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_84]), c_0_71]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_129, negated_conjecture, (k4_lattices(esk4_0,X1,X2)=k4_lattices(esk4_0,X2,X1)|~l1_lattices(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~m1_subset_1(X2,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 49.95/50.15  cnf(c_0_130, negated_conjecture, (k4_lattices(esk4_0,k7_lattices(esk4_0,k4_lattices(esk4_0,X1,k5_lattices(esk4_0))),k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k7_lattices(esk4_0,esk6_0)))=k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k7_lattices(esk4_0,esk6_0))|~m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_119]), c_0_84])])).
% 49.95/50.15  cnf(c_0_131, negated_conjecture, (k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k7_lattices(esk4_0,X1))=k7_lattices(esk4_0,k4_lattices(esk4_0,X1,esk5_0))|~m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))|~l2_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_65]), c_0_67]), c_0_54])]), c_0_30])).
% 49.95/50.15  cnf(c_0_132, negated_conjecture, (k4_lattices(esk4_0,esk5_0,k5_lattices(esk4_0))=k5_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_50]), c_0_122]), c_0_28]), c_0_29]), c_0_89])]), c_0_30])).
% 49.95/50.15  cnf(c_0_133, negated_conjecture, (k4_lattices(esk4_0,esk6_0,esk5_0)=k4_lattices(esk4_0,esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_45]), c_0_29])])).
% 49.95/50.15  cnf(c_0_134, negated_conjecture, (k4_lattices(esk4_0,k6_lattices(esk4_0),k7_lattices(esk4_0,k4_lattices(esk4_0,esk5_0,esk6_0)))=k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k4_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_52]), c_0_53]), c_0_50])])).
% 49.95/50.15  cnf(c_0_135, negated_conjecture, (k4_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0))=esk5_0|k5_lattices(esk4_0)=k4_lattices(esk4_0,esk5_0,esk6_0)|~l1_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_53]), c_0_50]), c_0_35])]), c_0_30])).
% 49.95/50.15  cnf(c_0_136, negated_conjecture, (k3_lattices(esk4_0,k5_lattices(esk4_0),k5_lattices(esk4_0))=k5_lattices(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_114]), c_0_114]), c_0_84])])).
% 49.95/50.15  cnf(c_0_137, negated_conjecture, (k4_lattices(esk4_0,X1,X2)=k4_lattices(esk4_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~m1_subset_1(X2,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_45]), c_0_29])])).
% 49.95/50.15  cnf(c_0_138, negated_conjecture, (k4_lattices(esk4_0,esk6_0,k6_lattices(esk4_0))=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_57]), c_0_34]), c_0_71]), c_0_28]), c_0_29]), c_0_84])]), c_0_30])).
% 49.95/50.15  cnf(c_0_139, negated_conjecture, (k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k4_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0)))=k7_lattices(esk4_0,k4_lattices(esk4_0,esk5_0,esk6_0))|~l2_lattices(esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_132]), c_0_101]), c_0_67]), c_0_50]), c_0_53]), c_0_34])]), c_0_133]), c_0_134]), c_0_133])).
% 49.95/50.15  cnf(c_0_140, negated_conjecture, (k4_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0))=esk5_0|k5_lattices(esk4_0)=k4_lattices(esk4_0,esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_45]), c_0_29])])).
% 49.95/50.15  cnf(c_0_141, negated_conjecture, (k7_lattices(esk4_0,k7_lattices(esk4_0,esk6_0))=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_34]), c_0_40]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_142, negated_conjecture, (k3_lattices(esk4_0,k5_lattices(esk4_0),k4_lattices(esk4_0,X1,k5_lattices(esk4_0)))=k4_lattices(esk4_0,k3_lattices(esk4_0,k5_lattices(esk4_0),X1),k5_lattices(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_136]), c_0_89]), c_0_105]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_143, negated_conjecture, (k4_lattices(esk4_0,X1,k5_lattices(esk4_0))=k5_lattices(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_137]), c_0_122]), c_0_28]), c_0_29]), c_0_89])]), c_0_30])).
% 49.95/50.15  cnf(c_0_144, negated_conjecture, (k4_lattices(esk4_0,k6_lattices(esk4_0),esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_50]), c_0_28]), c_0_29])]), c_0_30]), c_0_71])])).
% 49.95/50.15  cnf(c_0_145, negated_conjecture, (k4_lattices(esk4_0,k3_lattices(esk4_0,X1,X2),k3_lattices(esk4_0,X1,k5_lattices(esk4_0)))=k3_lattices(esk4_0,X1,k4_lattices(esk4_0,X2,k5_lattices(esk4_0)))|~m1_subset_1(X2,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_89]), c_0_105]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_146, negated_conjecture, (k3_lattices(esk4_0,k7_lattices(esk4_0,esk6_0),k5_lattices(esk4_0))=k7_lattices(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_138]), c_0_34])])).
% 49.95/50.15  cnf(c_0_147, negated_conjecture, (k4_lattices(esk4_0,k5_lattices(esk4_0),k5_lattices(esk4_0))=k5_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_89]), c_0_122]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_148, negated_conjecture, (k7_lattices(esk4_0,k4_lattices(esk4_0,esk5_0,esk6_0))=k6_lattices(esk4_0)|k5_lattices(esk4_0)=k4_lattices(esk4_0,esk5_0,esk6_0)|~l2_lattices(esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_110])).
% 49.95/50.15  cnf(c_0_149, negated_conjecture, (k7_lattices(esk4_0,k4_lattices(esk4_0,k7_lattices(esk4_0,esk6_0),X1))=k3_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,X1))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_141]), c_0_53]), c_0_40]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  fof(c_0_150, plain, ![X34, X35, X36]:(v2_struct_0(X34)|~v4_lattices(X34)|~l2_lattices(X34)|~m1_subset_1(X35,u1_struct_0(X34))|~m1_subset_1(X36,u1_struct_0(X34))|k3_lattices(X34,X35,X36)=k1_lattices(X34,X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).
% 49.95/50.15  cnf(c_0_151, negated_conjecture, (k4_lattices(esk4_0,k3_lattices(esk4_0,k5_lattices(esk4_0),X1),k5_lattices(esk4_0))=k5_lattices(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_136])).
% 49.95/50.15  cnf(c_0_152, negated_conjecture, (k3_lattices(esk4_0,k5_lattices(esk4_0),k7_lattices(esk4_0,esk5_0))=k7_lattices(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_114]), c_0_144]), c_0_84])])).
% 49.95/50.15  cnf(c_0_153, negated_conjecture, (k7_lattices(esk4_0,k4_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0)))=k3_lattices(esk4_0,k7_lattices(esk4_0,X1),esk6_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_53]), c_0_40]), c_0_28]), c_0_29])]), c_0_30]), c_0_141])).
% 49.95/50.15  cnf(c_0_154, negated_conjecture, (k4_lattices(esk4_0,k7_lattices(esk4_0,esk6_0),k7_lattices(esk4_0,esk6_0))=k7_lattices(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_146]), c_0_146]), c_0_147]), c_0_146]), c_0_89]), c_0_53])])).
% 49.95/50.15  cnf(c_0_155, negated_conjecture, (k7_lattices(esk4_0,k4_lattices(esk4_0,esk5_0,esk6_0))=k6_lattices(esk4_0)|k5_lattices(esk4_0)=k4_lattices(esk4_0,esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_61]), c_0_29])])).
% 49.95/50.15  cnf(c_0_156, negated_conjecture, (k4_lattices(esk4_0,k3_lattices(esk4_0,X1,X2),k3_lattices(esk4_0,X1,esk6_0))=k3_lattices(esk4_0,X1,k4_lattices(esk4_0,X2,esk6_0))|~m1_subset_1(X2,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_34]), c_0_28]), c_0_29])]), c_0_30]), c_0_105])])).
% 49.95/50.15  cnf(c_0_157, negated_conjecture, (k4_lattices(esk4_0,k6_lattices(esk4_0),esk6_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_34]), c_0_28]), c_0_29])]), c_0_30]), c_0_71])])).
% 49.95/50.15  cnf(c_0_158, negated_conjecture, (k7_lattices(esk4_0,k4_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0)))=k3_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_121]), c_0_50]), c_0_53])])).
% 49.95/50.15  cnf(c_0_159, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 49.95/50.15  fof(c_0_160, plain, ![X21, X22, X23]:((~v9_lattices(X21)|(~m1_subset_1(X22,u1_struct_0(X21))|(~m1_subset_1(X23,u1_struct_0(X21))|k2_lattices(X21,X22,k1_lattices(X21,X22,X23))=X22))|(v2_struct_0(X21)|~l3_lattices(X21)))&((m1_subset_1(esk2_1(X21),u1_struct_0(X21))|v9_lattices(X21)|(v2_struct_0(X21)|~l3_lattices(X21)))&((m1_subset_1(esk3_1(X21),u1_struct_0(X21))|v9_lattices(X21)|(v2_struct_0(X21)|~l3_lattices(X21)))&(k2_lattices(X21,esk2_1(X21),k1_lattices(X21,esk2_1(X21),esk3_1(X21)))!=esk2_1(X21)|v9_lattices(X21)|(v2_struct_0(X21)|~l3_lattices(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).
% 49.95/50.15  cnf(c_0_161, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_150])).
% 49.95/50.15  cnf(c_0_162, negated_conjecture, (k4_lattices(esk4_0,k7_lattices(esk4_0,k4_lattices(esk4_0,X1,esk5_0)),k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k5_lattices(esk4_0)))=k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k4_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k5_lattices(esk4_0)))|~m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_65]), c_0_67])])).
% 49.95/50.15  cnf(c_0_163, negated_conjecture, (k4_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k5_lattices(esk4_0))=k5_lattices(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_152]), c_0_67])])).
% 49.95/50.15  cnf(c_0_164, negated_conjecture, (k3_lattices(esk4_0,esk6_0,esk6_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_154]), c_0_141]), c_0_141]), c_0_53])])).
% 49.95/50.15  cnf(c_0_165, negated_conjecture, (k3_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk6_0))=k6_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_141]), c_0_53]), c_0_40]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_166, negated_conjecture, (k4_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk6_0))=k5_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_141]), c_0_53]), c_0_40]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_167, negated_conjecture, (k4_lattices(esk4_0,esk5_0,k6_lattices(esk4_0))=esk5_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_121]), c_0_50]), c_0_71]), c_0_28]), c_0_29]), c_0_84])]), c_0_30])).
% 49.95/50.15  cnf(c_0_168, negated_conjecture, (k5_lattices(esk4_0)=k4_lattices(esk4_0,esk5_0,esk6_0)|~l1_lattices(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_155]), c_0_114]), c_0_50])])).
% 49.95/50.15  cnf(c_0_169, negated_conjecture, (k4_lattices(esk4_0,k7_lattices(esk4_0,k4_lattices(esk4_0,X1,k5_lattices(esk4_0))),k3_lattices(esk4_0,k7_lattices(esk4_0,X1),esk6_0))=k3_lattices(esk4_0,k7_lattices(esk4_0,X1),esk6_0)|~m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_118]), c_0_157]), c_0_84])])).
% 49.95/50.15  cnf(c_0_170, negated_conjecture, (k4_lattices(esk4_0,k6_lattices(esk4_0),k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),esk6_0))=k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k4_lattices(esk4_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_110]), c_0_50]), c_0_67])])).
% 49.95/50.15  cnf(c_0_171, negated_conjecture, (k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),esk6_0)=k3_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_158]), c_0_50])])).
% 49.95/50.15  cnf(c_0_172, negated_conjecture, (k4_lattices(esk4_0,k7_lattices(esk4_0,k4_lattices(esk4_0,X1,esk5_0)),k3_lattices(esk4_0,k7_lattices(esk4_0,X1),X2))=k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k4_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),X2))|~m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))|~m1_subset_1(X2,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_65]), c_0_67]), c_0_105]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_173, negated_conjecture, (k4_lattices(esk4_0,k3_lattices(esk4_0,X1,X2),k3_lattices(esk4_0,X1,k7_lattices(esk4_0,esk5_0)))=k3_lattices(esk4_0,X1,k4_lattices(esk4_0,X2,k7_lattices(esk4_0,esk5_0)))|~m1_subset_1(X2,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_67]), c_0_105]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_174, negated_conjecture, (k3_lattices(esk4_0,k5_lattices(esk4_0),esk6_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_119]), c_0_141]), c_0_114]), c_0_84])])).
% 49.95/50.15  cnf(c_0_175, negated_conjecture, (k4_lattices(esk4_0,esk5_0,esk6_0)!=k5_lattices(esk4_0)|~r3_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 49.95/50.15  cnf(c_0_176, negated_conjecture, (r3_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))|~r1_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_53]), c_0_87]), c_0_88]), c_0_35]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_177, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k2_lattices(X1,X2,X3)!=X2|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 49.95/50.15  cnf(c_0_178, plain, (k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2|v2_struct_0(X1)|~v9_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_160])).
% 49.95/50.15  cnf(c_0_179, negated_conjecture, (k1_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))=k3_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))|~l2_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_53]), c_0_54])]), c_0_30])).
% 49.95/50.15  cnf(c_0_180, negated_conjecture, (k3_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))=k3_lattices(esk4_0,k7_lattices(esk4_0,esk6_0),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~l2_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_53]), c_0_54])]), c_0_30])).
% 49.95/50.15  cnf(c_0_181, negated_conjecture, (k4_lattices(esk4_0,k7_lattices(esk4_0,k4_lattices(esk4_0,X1,esk5_0)),k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k5_lattices(esk4_0)))=k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k5_lattices(esk4_0))|~m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_162, c_0_163])).
% 49.95/50.15  cnf(c_0_182, negated_conjecture, (k7_lattices(esk4_0,k4_lattices(esk4_0,k7_lattices(esk4_0,esk6_0),esk5_0))=k3_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_141]), c_0_53])])).
% 49.95/50.15  cnf(c_0_183, negated_conjecture, (k3_lattices(esk4_0,esk6_0,k5_lattices(esk4_0))=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_164]), c_0_165]), c_0_138]), c_0_166]), c_0_34])])).
% 49.95/50.15  cnf(c_0_184, negated_conjecture, (k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k5_lattices(esk4_0))=k7_lattices(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_167]), c_0_50])])).
% 49.95/50.15  cnf(c_0_185, negated_conjecture, (k5_lattices(esk4_0)=k4_lattices(esk4_0,esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168, c_0_45]), c_0_29])])).
% 49.95/50.15  cnf(c_0_186, negated_conjecture, (k3_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k4_lattices(esk4_0,esk5_0,esk6_0))=k3_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_132]), c_0_101]), c_0_170]), c_0_67]), c_0_50])]), c_0_171])).
% 49.95/50.15  cnf(c_0_187, negated_conjecture, (k3_lattices(esk4_0,k5_lattices(esk4_0),k4_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),X1))=k4_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),k3_lattices(esk4_0,k5_lattices(esk4_0),X1))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172, c_0_114]), c_0_144]), c_0_89]), c_0_84])])).
% 49.95/50.15  cnf(c_0_188, negated_conjecture, (k3_lattices(esk4_0,k5_lattices(esk4_0),k4_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0)))=k4_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_174]), c_0_34]), c_0_89])]), c_0_152])).
% 49.95/50.15  cnf(c_0_189, negated_conjecture, (k5_lattices(esk4_0)!=k4_lattices(esk4_0,esk5_0,esk6_0)|~r1_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175, c_0_176]), c_0_50])])).
% 49.95/50.15  cnf(c_0_190, negated_conjecture, (r1_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))|k2_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0))!=X1|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177, c_0_53]), c_0_87]), c_0_88]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_191, negated_conjecture, (k2_lattices(esk4_0,X1,k3_lattices(esk4_0,X1,k7_lattices(esk4_0,esk6_0)))=X1|~m1_subset_1(X1,u1_struct_0(esk4_0))|~l2_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178, c_0_179]), c_0_53]), c_0_87]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_192, negated_conjecture, (k3_lattices(esk4_0,k7_lattices(esk4_0,X1),k7_lattices(esk4_0,esk6_0))=k7_lattices(esk4_0,k4_lattices(esk4_0,esk6_0,X1))|~m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))|~l2_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_180]), c_0_34]), c_0_40]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_193, negated_conjecture, (k4_lattices(esk4_0,k3_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0)),esk6_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_141]), c_0_182]), c_0_183]), c_0_183]), c_0_34]), c_0_53])])).
% 49.95/50.15  cnf(c_0_194, negated_conjecture, (k3_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0))=k7_lattices(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_184, c_0_185]), c_0_186])).
% 49.95/50.15  cnf(c_0_195, negated_conjecture, (k4_lattices(esk4_0,k7_lattices(esk4_0,esk5_0),esk6_0)=k4_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187, c_0_57]), c_0_188]), c_0_174]), c_0_34]), c_0_67])])).
% 49.95/50.15  cnf(c_0_196, negated_conjecture, (k2_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0))!=esk5_0|k5_lattices(esk4_0)!=k4_lattices(esk4_0,esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189, c_0_190]), c_0_50])])).
% 49.95/50.15  cnf(c_0_197, negated_conjecture, (k2_lattices(esk4_0,k7_lattices(esk4_0,X1),k7_lattices(esk4_0,k4_lattices(esk4_0,esk6_0,X1)))=k7_lattices(esk4_0,X1)|~m1_subset_1(k7_lattices(esk4_0,X1),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))|~l2_lattices(esk4_0)), inference(spm,[status(thm)],[c_0_191, c_0_192])).
% 49.95/50.15  cnf(c_0_198, negated_conjecture, (k4_lattices(esk4_0,esk6_0,k7_lattices(esk4_0,esk5_0))=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_193, c_0_194]), c_0_195])).
% 49.95/50.15  cnf(c_0_199, negated_conjecture, (k7_lattices(esk4_0,k7_lattices(esk4_0,esk5_0))=esk5_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_50]), c_0_40]), c_0_28]), c_0_29])]), c_0_30])).
% 49.95/50.15  cnf(c_0_200, negated_conjecture, (k2_lattices(esk4_0,esk5_0,k7_lattices(esk4_0,esk6_0))!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_196, c_0_185])])).
% 49.95/50.15  cnf(c_0_201, negated_conjecture, (~l2_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197, c_0_198]), c_0_199]), c_0_199]), c_0_199]), c_0_50]), c_0_67])]), c_0_200])).
% 49.95/50.15  cnf(c_0_202, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201, c_0_61]), c_0_29])]), ['proof']).
% 49.95/50.15  # SZS output end CNFRefutation
% 49.95/50.15  # Proof object total steps             : 203
% 49.95/50.15  # Proof object clause steps            : 156
% 49.95/50.15  # Proof object formula steps           : 47
% 49.95/50.15  # Proof object conjectures             : 127
% 49.95/50.15  # Proof object clause conjectures      : 124
% 49.95/50.15  # Proof object formula conjectures     : 3
% 49.95/50.15  # Proof object initial clauses used    : 38
% 49.95/50.15  # Proof object initial formulas used   : 23
% 49.95/50.15  # Proof object generating inferences   : 113
% 49.95/50.15  # Proof object simplifying inferences  : 449
% 49.95/50.15  # Training examples: 0 positive, 0 negative
% 49.95/50.15  # Parsed axioms                        : 26
% 49.95/50.15  # Removed by relevancy pruning/SinE    : 0
% 49.95/50.15  # Initial clauses                      : 54
% 49.95/50.15  # Removed in clause preprocessing      : 3
% 49.95/50.15  # Initial clauses in saturation        : 51
% 49.95/50.15  # Processed clauses                    : 55671
% 49.95/50.15  # ...of these trivial                  : 1857
% 49.95/50.15  # ...subsumed                          : 43304
% 49.95/50.15  # ...remaining for further processing  : 10510
% 49.95/50.15  # Other redundant clauses eliminated   : 0
% 49.95/50.15  # Clauses deleted for lack of memory   : 85739
% 49.95/50.15  # Backward-subsumed                    : 1636
% 49.95/50.15  # Backward-rewritten                   : 4985
% 49.95/50.15  # Generated clauses                    : 2366680
% 49.95/50.15  # ...of the previous two non-trivial   : 2219374
% 49.95/50.15  # Contextual simplify-reflections      : 3862
% 49.95/50.15  # Paramodulations                      : 2366633
% 49.95/50.15  # Factorizations                       : 0
% 49.95/50.15  # Equation resolutions                 : 6
% 49.95/50.15  # Propositional unsat checks           : 0
% 49.95/50.15  #    Propositional check models        : 0
% 49.95/50.15  #    Propositional check unsatisfiable : 0
% 49.95/50.15  #    Propositional clauses             : 0
% 49.95/50.15  #    Propositional clauses after purity: 0
% 49.95/50.15  #    Propositional unsat core size     : 0
% 49.95/50.15  #    Propositional preprocessing time  : 0.000
% 49.95/50.15  #    Propositional encoding time       : 0.000
% 49.95/50.15  #    Propositional solver time         : 0.000
% 49.95/50.15  #    Success case prop preproc time    : 0.000
% 49.95/50.15  #    Success case prop encoding time   : 0.000
% 49.95/50.15  #    Success case prop solver time     : 0.000
% 49.95/50.15  # Current number of processed clauses  : 3848
% 49.95/50.15  #    Positive orientable unit clauses  : 190
% 49.95/50.15  #    Positive unorientable unit clauses: 0
% 49.95/50.15  #    Negative unit clauses             : 12
% 49.95/50.15  #    Non-unit-clauses                  : 3646
% 49.95/50.15  # Current number of unprocessed clauses: 1306581
% 49.95/50.15  # ...number of literals in the above   : 7214453
% 49.95/50.15  # Current number of archived formulas  : 0
% 49.95/50.15  # Current number of archived clauses   : 6662
% 49.95/50.15  # Clause-clause subsumption calls (NU) : 14200477
% 49.95/50.15  # Rec. Clause-clause subsumption calls : 2438259
% 49.95/50.15  # Non-unit clause-clause subsumptions  : 34401
% 49.95/50.15  # Unit Clause-clause subsumption calls : 159012
% 49.95/50.15  # Rewrite failures with RHS unbound    : 0
% 49.95/50.15  # BW rewrite match attempts            : 18989
% 49.95/50.15  # BW rewrite match successes           : 113
% 49.95/50.15  # Condensation attempts                : 0
% 49.95/50.15  # Condensation successes               : 0
% 49.95/50.15  # Termbank termtop insertions          : 129057910
% 50.10/50.26  
% 50.10/50.26  # -------------------------------------------------
% 50.10/50.26  # User time                : 48.782 s
% 50.10/50.26  # System time              : 1.146 s
% 50.10/50.26  # Total time               : 49.928 s
% 50.10/50.26  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
