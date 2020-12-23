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

% Result     : Theorem 9.32s
% Output     : CNFRefutation 9.32s
% Verified   : 
% Statistics : Number of formulae       :  237 (29489 expanded)
%              Number of clauses        :  178 (9391 expanded)
%              Number of leaves         :   29 (7312 expanded)
%              Depth                    :   21
%              Number of atoms          :  887 (196290 expanded)
%              Number of equality atoms :  186 (24886 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(t18_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattices(X1,X2,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_lattices)).

fof(dt_k7_lattices,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

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

fof(t23_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => r1_lattices(X1,k4_lattices(X1,X2,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).

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

fof(d7_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v7_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => k2_lattices(X1,X2,k2_lattices(X1,X3,X4)) = k2_lattices(X1,k2_lattices(X1,X2,X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_lattices)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

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

fof(t51_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k7_lattices(X1,k3_lattices(X1,X2,X3)) = k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_lattices)).

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

fof(dt_k6_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => m1_subset_1(k6_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(t17_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k1_lattices(X1,X2,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).

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

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

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

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(cc4_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v15_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v13_lattices(X1)
          & v14_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_lattices)).

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

fof(commutativity_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

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

fof(t44_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v14_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k3_lattices(X1,k6_lattices(X1),X2) = k6_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_lattices)).

fof(t39_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k3_lattices(X1,k5_lattices(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_lattices)).

fof(t34_lattices,axiom,(
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
                 => k4_lattices(X1,k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X3,X4)),k3_lattices(X1,X4,X2)) = k3_lattices(X1,k3_lattices(X1,k4_lattices(X1,X2,X3),k4_lattices(X1,X3,X4)),k4_lattices(X1,X4,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattices)).

fof(c_0_29,negated_conjecture,(
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

fof(c_0_30,plain,(
    ! [X7] :
      ( ( ~ v2_struct_0(X7)
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v4_lattices(X7)
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v5_lattices(X7)
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v6_lattices(X7)
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v7_lattices(X7)
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v8_lattices(X7)
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( v9_lattices(X7)
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ l3_lattices(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v10_lattices(esk6_0)
    & v17_lattices(esk6_0)
    & l3_lattices(esk6_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    & ( k4_lattices(esk6_0,esk7_0,esk8_0) != k5_lattices(esk6_0)
      | ~ r3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) )
    & ( k4_lattices(esk6_0,esk7_0,esk8_0) = k5_lattices(esk6_0)
      | r3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_29])])])])).

fof(c_0_32,plain,(
    ! [X44,X45] :
      ( v2_struct_0(X44)
      | ~ v6_lattices(X44)
      | ~ v8_lattices(X44)
      | ~ v9_lattices(X44)
      | ~ l3_lattices(X44)
      | ~ m1_subset_1(X45,u1_struct_0(X44))
      | k4_lattices(X44,X45,X45) = X45 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t18_lattices])])])])).

cnf(c_0_33,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( v10_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( l3_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_39,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ l3_lattices(X30)
      | ~ m1_subset_1(X31,u1_struct_0(X30))
      | m1_subset_1(k7_lattices(X30,X31),u1_struct_0(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).

fof(c_0_40,plain,(
    ! [X46,X47,X48] :
      ( ( ~ r1_lattices(X46,X47,X48)
        | k2_lattices(X46,X47,X48) = X47
        | ~ m1_subset_1(X48,u1_struct_0(X46))
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | v2_struct_0(X46)
        | ~ v8_lattices(X46)
        | ~ v9_lattices(X46)
        | ~ l3_lattices(X46) )
      & ( k2_lattices(X46,X47,X48) != X47
        | r1_lattices(X46,X47,X48)
        | ~ m1_subset_1(X48,u1_struct_0(X46))
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | v2_struct_0(X46)
        | ~ v8_lattices(X46)
        | ~ v9_lattices(X46)
        | ~ l3_lattices(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

fof(c_0_41,plain,(
    ! [X52,X53,X54] :
      ( v2_struct_0(X52)
      | ~ v6_lattices(X52)
      | ~ v8_lattices(X52)
      | ~ l3_lattices(X52)
      | ~ m1_subset_1(X53,u1_struct_0(X52))
      | ~ m1_subset_1(X54,u1_struct_0(X52))
      | r1_lattices(X52,k4_lattices(X52,X53,X54),X53) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_lattices])])])])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X2) = X2
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( v9_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( v8_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( v6_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_34]),c_0_35])]),c_0_36])).

fof(c_0_47,plain,(
    ! [X39,X40,X41] :
      ( ( ~ r3_lattices(X39,X40,X41)
        | r1_lattices(X39,X40,X41)
        | v2_struct_0(X39)
        | ~ v6_lattices(X39)
        | ~ v8_lattices(X39)
        | ~ v9_lattices(X39)
        | ~ l3_lattices(X39)
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | ~ m1_subset_1(X41,u1_struct_0(X39)) )
      & ( ~ r1_lattices(X39,X40,X41)
        | r3_lattices(X39,X40,X41)
        | v2_struct_0(X39)
        | ~ v6_lattices(X39)
        | ~ v8_lattices(X39)
        | ~ v9_lattices(X39)
        | ~ l3_lattices(X39)
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | ~ m1_subset_1(X41,u1_struct_0(X39)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_50,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,k4_lattices(X1,X2,X3),X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_35])]),c_0_36]),c_0_44]),c_0_45]),c_0_46])])).

fof(c_0_53,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ v7_lattices(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | k2_lattices(X16,X17,k2_lattices(X16,X18,X19)) = k2_lattices(X16,k2_lattices(X16,X17,X18),X19)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) )
      & ( m1_subset_1(esk1_1(X16),u1_struct_0(X16))
        | v7_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) )
      & ( m1_subset_1(esk2_1(X16),u1_struct_0(X16))
        | v7_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) )
      & ( m1_subset_1(esk3_1(X16),u1_struct_0(X16))
        | v7_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) )
      & ( k2_lattices(X16,esk1_1(X16),k2_lattices(X16,esk2_1(X16),esk3_1(X16))) != k2_lattices(X16,k2_lattices(X16,esk1_1(X16),esk2_1(X16)),esk3_1(X16))
        | v7_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_lattices])])])])])])).

cnf(c_0_54,plain,
    ( v7_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_55,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_35])]),c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( k2_lattices(esk6_0,X1,esk7_0) = X1
    | ~ r1_lattices(esk6_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_43]),c_0_35])]),c_0_36]),c_0_44]),c_0_45])])).

cnf(c_0_58,negated_conjecture,
    ( r1_lattices(esk6_0,esk7_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_43]),c_0_45]),c_0_46]),c_0_35])]),c_0_36])).

fof(c_0_59,plain,(
    ! [X36,X37,X38] :
      ( v2_struct_0(X36)
      | ~ v6_lattices(X36)
      | ~ l1_lattices(X36)
      | ~ m1_subset_1(X37,u1_struct_0(X36))
      | ~ m1_subset_1(X38,u1_struct_0(X36))
      | k4_lattices(X36,X37,X38) = k2_lattices(X36,X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

cnf(c_0_60,plain,
    ( k2_lattices(X1,X2,k2_lattices(X1,X3,X4)) = k2_lattices(X1,k2_lattices(X1,X2,X3),X4)
    | v2_struct_0(X1)
    | ~ v7_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( v7_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_34]),c_0_35])]),c_0_36])).

fof(c_0_62,plain,(
    ! [X79,X80] :
      ( v2_struct_0(X79)
      | ~ v10_lattices(X79)
      | ~ v17_lattices(X79)
      | ~ l3_lattices(X79)
      | ~ m1_subset_1(X80,u1_struct_0(X79))
      | k7_lattices(X79,k7_lattices(X79,X80)) = X80 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_lattices])])])])).

cnf(c_0_63,negated_conjecture,
    ( r1_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))
    | ~ r3_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_44]),c_0_45]),c_0_46]),c_0_35])]),c_0_36])).

cnf(c_0_64,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,esk8_0) = k5_lattices(esk6_0)
    | r3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_65,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_43])])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( k2_lattices(esk6_0,k2_lattices(esk6_0,X1,X2),esk8_0) = k2_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,esk8_0))
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_49]),c_0_36]),c_0_61])])).

fof(c_0_68,plain,(
    ! [X84,X85,X86] :
      ( v2_struct_0(X84)
      | ~ v10_lattices(X84)
      | ~ v17_lattices(X84)
      | ~ l3_lattices(X84)
      | ~ m1_subset_1(X85,u1_struct_0(X84))
      | ~ m1_subset_1(X86,u1_struct_0(X84))
      | k7_lattices(X84,k3_lattices(X84,X85,X86)) = k4_lattices(X84,k7_lattices(X84,X85),k7_lattices(X84,X86)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t51_lattices])])])])).

fof(c_0_69,plain,(
    ! [X77,X78] :
      ( v2_struct_0(X77)
      | ~ v10_lattices(X77)
      | ~ v17_lattices(X77)
      | ~ l3_lattices(X77)
      | ~ m1_subset_1(X78,u1_struct_0(X77))
      | k3_lattices(X77,k7_lattices(X77,X78),X78) = k6_lattices(X77) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattices])])])])).

fof(c_0_70,plain,(
    ! [X29] :
      ( v2_struct_0(X29)
      | ~ l2_lattices(X29)
      | m1_subset_1(k6_lattices(X29),u1_struct_0(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_lattices])])])).

fof(c_0_71,plain,(
    ! [X32] :
      ( ( l1_lattices(X32)
        | ~ l3_lattices(X32) )
      & ( l2_lattices(X32)
        | ~ l3_lattices(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_72,plain,(
    ! [X42,X43] :
      ( v2_struct_0(X42)
      | ~ v6_lattices(X42)
      | ~ v8_lattices(X42)
      | ~ v9_lattices(X42)
      | ~ l3_lattices(X42)
      | ~ m1_subset_1(X43,u1_struct_0(X42))
      | k1_lattices(X42,X43,X43) = X43 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_lattices])])])])).

fof(c_0_73,plain,(
    ! [X9] :
      ( ( ~ v2_struct_0(X9)
        | v2_struct_0(X9)
        | ~ v17_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v11_lattices(X9)
        | v2_struct_0(X9)
        | ~ v17_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v15_lattices(X9)
        | v2_struct_0(X9)
        | ~ v17_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v16_lattices(X9)
        | v2_struct_0(X9)
        | ~ v17_lattices(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_lattices])])])])).

cnf(c_0_74,plain,
    ( v2_struct_0(X1)
    | k7_lattices(X1,k7_lattices(X1,X2)) = X2
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( v17_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_76,plain,(
    ! [X81,X82,X83] :
      ( v2_struct_0(X81)
      | ~ v10_lattices(X81)
      | ~ v17_lattices(X81)
      | ~ l3_lattices(X81)
      | ~ m1_subset_1(X82,u1_struct_0(X81))
      | ~ m1_subset_1(X83,u1_struct_0(X81))
      | k7_lattices(X81,k4_lattices(X81,X82,X83)) = k3_lattices(X81,k7_lattices(X81,X82),k7_lattices(X81,X83)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_lattices])])])])).

fof(c_0_77,plain,(
    ! [X13,X14,X15] :
      ( v2_struct_0(X13)
      | ~ v6_lattices(X13)
      | ~ l1_lattices(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | k4_lattices(X13,X14,X15) = k4_lattices(X13,X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_78,negated_conjecture,
    ( k2_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0)) = X1
    | ~ r1_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_56]),c_0_44]),c_0_45]),c_0_35])]),c_0_36])).

cnf(c_0_79,negated_conjecture,
    ( k5_lattices(esk6_0) = k4_lattices(esk6_0,esk7_0,esk8_0)
    | r1_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_43])])).

cnf(c_0_80,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k2_lattices(esk6_0,esk7_0,X1)) = k2_lattices(esk6_0,esk7_0,X1)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_65]),c_0_43]),c_0_61])]),c_0_36])).

cnf(c_0_81,negated_conjecture,
    ( k2_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,esk8_0)) = k4_lattices(esk6_0,k2_lattices(esk6_0,X1,X2),esk8_0)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(k2_lattices(esk6_0,X1,X2),u1_struct_0(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_49]),c_0_46])]),c_0_36])).

fof(c_0_82,plain,(
    ! [X28] :
      ( v2_struct_0(X28)
      | ~ l1_lattices(X28)
      | m1_subset_1(k5_lattices(X28),u1_struct_0(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_83,plain,(
    ! [X75,X76] :
      ( v2_struct_0(X75)
      | ~ v10_lattices(X75)
      | ~ v17_lattices(X75)
      | ~ l3_lattices(X75)
      | ~ m1_subset_1(X76,u1_struct_0(X75))
      | k4_lattices(X75,k7_lattices(X75,X76),X76) = k5_lattices(X75) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattices])])])])).

cnf(c_0_84,plain,
    ( v2_struct_0(X1)
    | k7_lattices(X1,k3_lattices(X1,X2,X3)) = k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,k7_lattices(X1,X2),X2) = k6_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_86,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_87,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

fof(c_0_88,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ v4_lattices(X33)
      | ~ l2_lattices(X33)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | ~ m1_subset_1(X35,u1_struct_0(X33))
      | k3_lattices(X33,X34,X35) = k1_lattices(X33,X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

cnf(c_0_89,plain,
    ( v2_struct_0(X1)
    | k1_lattices(X1,X2,X2) = X2
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_90,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_91,plain,(
    ! [X8] :
      ( ( ~ v2_struct_0(X8)
        | v2_struct_0(X8)
        | ~ v15_lattices(X8)
        | ~ l3_lattices(X8) )
      & ( v13_lattices(X8)
        | v2_struct_0(X8)
        | ~ v15_lattices(X8)
        | ~ l3_lattices(X8) )
      & ( v14_lattices(X8)
        | v2_struct_0(X8)
        | ~ v15_lattices(X8)
        | ~ l3_lattices(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_lattices])])])])).

cnf(c_0_92,plain,
    ( v15_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_93,negated_conjecture,
    ( k7_lattices(esk6_0,k7_lattices(esk6_0,esk8_0)) = esk8_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_49]),c_0_75]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_94,plain,
    ( v2_struct_0(X1)
    | k7_lattices(X1,k4_lattices(X1,X2,X3)) = k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_95,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_96,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) = esk7_0
    | k5_lattices(esk6_0) = k4_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_43])])).

cnf(c_0_97,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,esk8_0) = k4_lattices(esk6_0,esk7_0,esk8_0)
    | ~ l1_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_65]),c_0_49]),c_0_65]),c_0_43]),c_0_43])])).

cnf(c_0_98,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_99,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_100,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,k7_lattices(X1,X2),X2) = k5_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_101,negated_conjecture,
    ( k4_lattices(esk6_0,k7_lattices(esk6_0,X1),k7_lattices(esk6_0,esk8_0)) = k7_lattices(esk6_0,k3_lattices(esk6_0,X1,esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_49]),c_0_75]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_102,negated_conjecture,
    ( k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk8_0) = k6_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_49]),c_0_75]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_103,plain,
    ( m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

fof(c_0_104,plain,(
    ! [X59,X60,X61,X62] :
      ( v2_struct_0(X59)
      | ~ v10_lattices(X59)
      | ~ v11_lattices(X59)
      | ~ l3_lattices(X59)
      | ~ m1_subset_1(X60,u1_struct_0(X59))
      | ~ m1_subset_1(X61,u1_struct_0(X59))
      | ~ m1_subset_1(X62,u1_struct_0(X59))
      | k3_lattices(X59,X60,k4_lattices(X59,X61,X62)) = k4_lattices(X59,k3_lattices(X59,X60,X61),k3_lattices(X59,X60,X62)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_lattices])])])])).

cnf(c_0_105,plain,
    ( v11_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_106,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_107,negated_conjecture,
    ( k1_lattices(esk6_0,esk7_0,esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_43]),c_0_35])]),c_0_36]),c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_108,negated_conjecture,
    ( v4_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_34]),c_0_35])]),c_0_36])).

fof(c_0_109,plain,(
    ! [X71,X72] :
      ( v2_struct_0(X71)
      | ~ v10_lattices(X71)
      | ~ v14_lattices(X71)
      | ~ l3_lattices(X71)
      | ~ m1_subset_1(X72,u1_struct_0(X71))
      | k4_lattices(X71,k6_lattices(X71),X72) = X72 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_lattices])])])])).

cnf(c_0_110,plain,
    ( v14_lattices(X1)
    | v2_struct_0(X1)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_111,negated_conjecture,
    ( v15_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_75]),c_0_35])]),c_0_36])).

fof(c_0_112,plain,(
    ! [X10,X11,X12] :
      ( v2_struct_0(X10)
      | ~ v4_lattices(X10)
      | ~ l2_lattices(X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | k3_lattices(X10,X11,X12) = k3_lattices(X10,X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).

cnf(c_0_113,negated_conjecture,
    ( k7_lattices(esk6_0,k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),X1)) = k4_lattices(esk6_0,esk8_0,k7_lattices(esk6_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_93]),c_0_56]),c_0_75]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_114,negated_conjecture,
    ( k3_lattices(esk6_0,k7_lattices(esk6_0,X1),k7_lattices(esk6_0,esk7_0)) = k7_lattices(esk6_0,k4_lattices(esk6_0,X1,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_43]),c_0_75]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_115,negated_conjecture,
    ( k7_lattices(esk6_0,k7_lattices(esk6_0,esk7_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_43]),c_0_75]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_116,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_43]),c_0_35])]),c_0_36])).

cnf(c_0_117,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk7_0) = k4_lattices(esk6_0,esk7_0,X1)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_43]),c_0_36]),c_0_46])])).

cnf(c_0_118,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k2_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk8_0)) = k2_lattices(esk6_0,esk7_0,esk8_0)
    | k5_lattices(esk6_0) = k4_lattices(esk6_0,esk7_0,esk8_0)
    | ~ l1_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_96]),c_0_56]),c_0_43])])).

cnf(c_0_119,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,esk8_0) = k4_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_35])])).

cnf(c_0_120,plain,
    ( m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_98])).

cnf(c_0_121,negated_conjecture,
    ( k7_lattices(esk6_0,k6_lattices(esk6_0)) = k5_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102]),c_0_56]),c_0_75]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_122,negated_conjecture,
    ( m1_subset_1(k6_lattices(esk6_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_35]),c_0_36])).

cnf(c_0_123,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,k4_lattices(X1,X3,X4)) = k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X2,X4))
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_124,negated_conjecture,
    ( v11_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_75]),c_0_35])]),c_0_36])).

cnf(c_0_125,negated_conjecture,
    ( k3_lattices(esk6_0,esk7_0,esk7_0) = esk7_0
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_43]),c_0_108])]),c_0_36])).

cnf(c_0_126,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,k6_lattices(X1),X2) = X2
    | ~ v10_lattices(X1)
    | ~ v14_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_127,negated_conjecture,
    ( v14_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_35])]),c_0_36])).

cnf(c_0_128,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_129,negated_conjecture,
    ( k3_lattices(esk6_0,k7_lattices(esk6_0,X1),k7_lattices(esk6_0,esk8_0)) = k7_lattices(esk6_0,k4_lattices(esk6_0,X1,esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_49]),c_0_75]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_130,negated_conjecture,
    ( k7_lattices(esk6_0,k7_lattices(esk6_0,k4_lattices(esk6_0,esk8_0,esk7_0))) = k4_lattices(esk6_0,esk8_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115]),c_0_116]),c_0_49])])).

cnf(c_0_131,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk7_0) = k4_lattices(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_98]),c_0_35])])).

cnf(c_0_132,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k2_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk8_0)) = k4_lattices(esk6_0,esk7_0,esk8_0)
    | k5_lattices(esk6_0) = k4_lattices(esk6_0,esk7_0,esk8_0)
    | ~ l1_lattices(esk6_0) ),
    inference(rw,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_133,negated_conjecture,
    ( k2_lattices(esk6_0,X1,esk8_0) = k4_lattices(esk6_0,X1,esk8_0)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_49]),c_0_36]),c_0_46])])).

fof(c_0_134,plain,(
    ! [X69,X70] :
      ( v2_struct_0(X69)
      | ~ v10_lattices(X69)
      | ~ v13_lattices(X69)
      | ~ l3_lattices(X69)
      | ~ m1_subset_1(X70,u1_struct_0(X69))
      | k4_lattices(X69,k5_lattices(X69),X70) = k5_lattices(X69) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_lattices])])])])).

cnf(c_0_135,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_136,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) = esk7_0
    | k5_lattices(esk6_0) = k4_lattices(esk6_0,esk7_0,esk8_0)
    | ~ l1_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_96]),c_0_56]),c_0_43]),c_0_46])]),c_0_36])).

cnf(c_0_137,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk6_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_35]),c_0_36])).

cnf(c_0_138,negated_conjecture,
    ( k7_lattices(esk6_0,k5_lattices(esk6_0)) = k6_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_121]),c_0_122]),c_0_75]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_139,negated_conjecture,
    ( k4_lattices(esk6_0,k3_lattices(esk6_0,X1,X2),k3_lattices(esk6_0,X1,esk7_0)) = k3_lattices(esk6_0,X1,k4_lattices(esk6_0,X2,esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_43]),c_0_34]),c_0_35])]),c_0_36]),c_0_124])])).

cnf(c_0_140,negated_conjecture,
    ( k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk7_0)) = k6_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_115]),c_0_116]),c_0_75]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_141,negated_conjecture,
    ( k3_lattices(esk6_0,esk7_0,esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_87]),c_0_35])])).

cnf(c_0_142,negated_conjecture,
    ( k4_lattices(esk6_0,k6_lattices(esk6_0),esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_43]),c_0_34]),c_0_35])]),c_0_36]),c_0_127])])).

cnf(c_0_143,negated_conjecture,
    ( k4_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),esk7_0) = k5_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_43]),c_0_75]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_144,negated_conjecture,
    ( k7_lattices(esk6_0,k3_lattices(esk6_0,X1,k7_lattices(esk6_0,esk7_0))) = k4_lattices(esk6_0,k7_lattices(esk6_0,X1),esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_116]),c_0_75]),c_0_34]),c_0_35])]),c_0_36]),c_0_115])).

cnf(c_0_145,negated_conjecture,
    ( k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),k7_lattices(esk6_0,X1)) = k7_lattices(esk6_0,k4_lattices(esk6_0,X1,esk8_0))
    | ~ m1_subset_1(k7_lattices(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_56]),c_0_108])]),c_0_36])).

cnf(c_0_146,negated_conjecture,
    ( k7_lattices(esk6_0,k7_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0))) = k4_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_49])])).

cnf(c_0_147,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k2_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk8_0)) = k4_lattices(esk6_0,esk7_0,esk8_0)
    | k5_lattices(esk6_0) = k4_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_98]),c_0_35])])).

cnf(c_0_148,negated_conjecture,
    ( k2_lattices(esk6_0,X1,esk8_0) = k4_lattices(esk6_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_98]),c_0_35])])).

cnf(c_0_149,negated_conjecture,
    ( k4_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk8_0) = k5_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_49]),c_0_75]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_150,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,k5_lattices(X1),X2) = k5_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_134])).

cnf(c_0_151,negated_conjecture,
    ( v13_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_111]),c_0_35])]),c_0_36])).

fof(c_0_152,plain,(
    ! [X73,X74] :
      ( v2_struct_0(X73)
      | ~ v10_lattices(X73)
      | ~ v14_lattices(X73)
      | ~ l3_lattices(X73)
      | ~ m1_subset_1(X74,u1_struct_0(X73))
      | k3_lattices(X73,k6_lattices(X73),X74) = k6_lattices(X73) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_lattices])])])])).

cnf(c_0_153,negated_conjecture,
    ( k3_lattices(esk6_0,X1,esk8_0) = k3_lattices(esk6_0,esk8_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_49]),c_0_36]),c_0_108])])).

cnf(c_0_154,negated_conjecture,
    ( k7_lattices(esk6_0,k4_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))) = k3_lattices(esk6_0,k7_lattices(esk6_0,X1),esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_56]),c_0_75]),c_0_34]),c_0_35])]),c_0_36]),c_0_93])).

cnf(c_0_155,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) = esk7_0
    | k5_lattices(esk6_0) = k4_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_98]),c_0_35])])).

cnf(c_0_156,negated_conjecture,
    ( k7_lattices(esk6_0,k3_lattices(esk6_0,X1,k5_lattices(esk6_0))) = k4_lattices(esk6_0,k7_lattices(esk6_0,X1),k6_lattices(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_137]),c_0_75]),c_0_34]),c_0_35])]),c_0_36]),c_0_138])).

cnf(c_0_157,negated_conjecture,
    ( k3_lattices(esk6_0,esk7_0,k5_lattices(esk6_0)) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_141]),c_0_142]),c_0_143]),c_0_116]),c_0_43])])).

cnf(c_0_158,negated_conjecture,
    ( k4_lattices(esk6_0,esk8_0,esk7_0) = k4_lattices(esk6_0,esk7_0,esk8_0)
    | ~ l2_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_145]),c_0_146]),c_0_93]),c_0_56]),c_0_116]),c_0_43])])).

cnf(c_0_159,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k5_lattices(esk6_0)) = k4_lattices(esk6_0,esk7_0,esk8_0)
    | k5_lattices(esk6_0) = k4_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_148]),c_0_149]),c_0_56])])).

cnf(c_0_160,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,k5_lattices(esk6_0)) = k5_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_131]),c_0_43]),c_0_151]),c_0_34]),c_0_35]),c_0_137])]),c_0_36])).

cnf(c_0_161,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,k6_lattices(X1),X2) = k6_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v14_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_152])).

cnf(c_0_162,negated_conjecture,
    ( k3_lattices(esk6_0,X1,esk8_0) = k3_lattices(esk6_0,esk8_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_87]),c_0_35])])).

cnf(c_0_163,negated_conjecture,
    ( k3_lattices(esk6_0,X1,k7_lattices(esk6_0,esk7_0)) = k3_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_116]),c_0_108])]),c_0_36])).

cnf(c_0_164,negated_conjecture,
    ( k3_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),esk8_0) = k7_lattices(esk6_0,esk7_0)
    | k5_lattices(esk6_0) = k4_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_155]),c_0_43])])).

cnf(c_0_165,negated_conjecture,
    ( k3_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),esk7_0) = k6_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_43]),c_0_75]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_166,negated_conjecture,
    ( k4_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),k6_lattices(esk6_0)) = k7_lattices(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_157]),c_0_43])])).

cnf(c_0_167,negated_conjecture,
    ( k4_lattices(esk6_0,esk8_0,esk7_0) = k4_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_87]),c_0_35])])).

cnf(c_0_168,negated_conjecture,
    ( k5_lattices(esk6_0) = k4_lattices(esk6_0,esk7_0,esk8_0)
    | ~ l1_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_159]),c_0_160]),c_0_137]),c_0_43]),c_0_46])]),c_0_36])).

cnf(c_0_169,negated_conjecture,
    ( k7_lattices(esk6_0,k4_lattices(esk6_0,X1,k6_lattices(esk6_0))) = k3_lattices(esk6_0,k7_lattices(esk6_0,X1),k5_lattices(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_122]),c_0_75]),c_0_34]),c_0_35])]),c_0_36]),c_0_121])).

cnf(c_0_170,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,k6_lattices(esk6_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_131]),c_0_43]),c_0_127]),c_0_34]),c_0_35]),c_0_122])]),c_0_36])).

cnf(c_0_171,negated_conjecture,
    ( k7_lattices(esk6_0,k3_lattices(esk6_0,X1,k6_lattices(esk6_0))) = k4_lattices(esk6_0,k7_lattices(esk6_0,X1),k5_lattices(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_122]),c_0_75]),c_0_34]),c_0_35])]),c_0_36]),c_0_121])).

cnf(c_0_172,negated_conjecture,
    ( k3_lattices(esk6_0,esk8_0,k6_lattices(esk6_0)) = k6_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_162]),c_0_49]),c_0_127]),c_0_34]),c_0_35]),c_0_122])]),c_0_36])).

cnf(c_0_173,negated_conjecture,
    ( k1_lattices(esk6_0,esk8_0,esk8_0) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_49]),c_0_35])]),c_0_36]),c_0_44]),c_0_45]),c_0_46])])).

fof(c_0_174,plain,(
    ! [X67,X68] :
      ( v2_struct_0(X67)
      | ~ v10_lattices(X67)
      | ~ v13_lattices(X67)
      | ~ l3_lattices(X67)
      | ~ m1_subset_1(X68,u1_struct_0(X67))
      | k3_lattices(X67,k5_lattices(X67),X68) = X68 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_lattices])])])])).

cnf(c_0_175,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk8_0) = k4_lattices(esk6_0,esk8_0,X1)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_49]),c_0_36]),c_0_46])])).

cnf(c_0_176,negated_conjecture,
    ( k7_lattices(esk6_0,k3_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),X1)) = k4_lattices(esk6_0,k7_lattices(esk6_0,X1),esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(spm,[status(thm)],[c_0_144,c_0_163])).

cnf(c_0_177,negated_conjecture,
    ( k3_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),k4_lattices(esk6_0,esk7_0,esk8_0)) = k7_lattices(esk6_0,esk7_0)
    | k5_lattices(esk6_0) = k4_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_164]),c_0_165]),c_0_49]),c_0_116])]),c_0_166]),c_0_167])).

cnf(c_0_178,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk6_0,esk7_0,esk8_0),u1_struct_0(esk6_0))
    | ~ l1_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_168]),c_0_36])).

cnf(c_0_179,negated_conjecture,
    ( k4_lattices(esk6_0,k7_lattices(esk6_0,k4_lattices(esk6_0,X1,esk8_0)),k3_lattices(esk6_0,k7_lattices(esk6_0,X1),X2)) = k3_lattices(esk6_0,k7_lattices(esk6_0,X1),k4_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),X2))
    | ~ m1_subset_1(k7_lattices(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_129]),c_0_56]),c_0_124]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_180,negated_conjecture,
    ( k3_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),k5_lattices(esk6_0)) = k7_lattices(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_170]),c_0_43])])).

cnf(c_0_181,negated_conjecture,
    ( k4_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),k5_lattices(esk6_0)) = k5_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_172]),c_0_121]),c_0_49])])).

fof(c_0_182,plain,(
    ! [X63,X64,X65,X66] :
      ( v2_struct_0(X63)
      | ~ v10_lattices(X63)
      | ~ v11_lattices(X63)
      | ~ l3_lattices(X63)
      | ~ m1_subset_1(X64,u1_struct_0(X63))
      | ~ m1_subset_1(X65,u1_struct_0(X63))
      | ~ m1_subset_1(X66,u1_struct_0(X63))
      | k4_lattices(X63,k4_lattices(X63,k3_lattices(X63,X64,X65),k3_lattices(X63,X65,X66)),k3_lattices(X63,X66,X64)) = k3_lattices(X63,k3_lattices(X63,k4_lattices(X63,X64,X65),k4_lattices(X63,X65,X66)),k4_lattices(X63,X66,X64)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattices])])])])).

cnf(c_0_183,negated_conjecture,
    ( k3_lattices(esk6_0,esk8_0,esk8_0) = esk8_0
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_173]),c_0_49]),c_0_108])]),c_0_36])).

cnf(c_0_184,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,k5_lattices(X1),X2) = X2
    | ~ v10_lattices(X1)
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_174])).

cnf(c_0_185,negated_conjecture,
    ( k7_lattices(esk6_0,k4_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),X1)) = k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_115]),c_0_116]),c_0_75]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_186,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk8_0) = k4_lattices(esk6_0,esk8_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_98]),c_0_35])])).

cnf(c_0_187,negated_conjecture,
    ( k4_lattices(esk6_0,k7_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0)),esk7_0) = esk7_0
    | k5_lattices(esk6_0) = k4_lattices(esk6_0,esk7_0,esk8_0)
    | ~ m1_subset_1(k4_lattices(esk6_0,esk7_0,esk8_0),u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_177]),c_0_115])).

cnf(c_0_188,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk6_0,esk7_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_98]),c_0_35])])).

cnf(c_0_189,negated_conjecture,
    ( k7_lattices(esk6_0,k4_lattices(esk6_0,X1,k7_lattices(esk6_0,esk7_0))) = k3_lattices(esk6_0,k7_lattices(esk6_0,X1),esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_116]),c_0_75]),c_0_34]),c_0_35])]),c_0_36]),c_0_115])).

cnf(c_0_190,negated_conjecture,
    ( k4_lattices(esk6_0,k7_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0)),k7_lattices(esk6_0,esk7_0)) = k7_lattices(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_180]),c_0_181]),c_0_180]),c_0_116]),c_0_137]),c_0_43])])).

cnf(c_0_191,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X3,X4)),k3_lattices(X1,X4,X2)) = k3_lattices(X1,k3_lattices(X1,k4_lattices(X1,X2,X3),k4_lattices(X1,X3,X4)),k4_lattices(X1,X4,X2))
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_182])).

cnf(c_0_192,negated_conjecture,
    ( k4_lattices(esk6_0,k3_lattices(esk6_0,X1,X2),k3_lattices(esk6_0,X1,esk8_0)) = k3_lattices(esk6_0,X1,k4_lattices(esk6_0,X2,esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_49]),c_0_34]),c_0_35])]),c_0_36]),c_0_124])])).

cnf(c_0_193,negated_conjecture,
    ( k3_lattices(esk6_0,esk8_0,k7_lattices(esk6_0,esk8_0)) = k6_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_93]),c_0_56]),c_0_75]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_194,negated_conjecture,
    ( k3_lattices(esk6_0,esk8_0,esk8_0) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_87]),c_0_35])])).

cnf(c_0_195,negated_conjecture,
    ( k4_lattices(esk6_0,k6_lattices(esk6_0),esk8_0) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_49]),c_0_34]),c_0_35])]),c_0_36]),c_0_127])])).

cnf(c_0_196,negated_conjecture,
    ( k3_lattices(esk6_0,k5_lattices(esk6_0),esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_43]),c_0_34]),c_0_35])]),c_0_36]),c_0_151])])).

cnf(c_0_197,negated_conjecture,
    ( k3_lattices(esk6_0,k5_lattices(esk6_0),esk8_0) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_49]),c_0_34]),c_0_35])]),c_0_36]),c_0_151])])).

cnf(c_0_198,negated_conjecture,
    ( k4_lattices(esk6_0,k5_lattices(esk6_0),esk8_0) = k5_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_49]),c_0_34]),c_0_35])]),c_0_36]),c_0_151])])).

cnf(c_0_199,negated_conjecture,
    ( k3_lattices(esk6_0,X1,esk7_0) = k3_lattices(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_43]),c_0_36]),c_0_108])])).

cnf(c_0_200,negated_conjecture,
    ( k7_lattices(esk6_0,k4_lattices(esk6_0,esk8_0,k7_lattices(esk6_0,esk7_0))) = k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_186]),c_0_49]),c_0_116])])).

cnf(c_0_201,negated_conjecture,
    ( k4_lattices(esk6_0,k3_lattices(esk6_0,X1,X2),k3_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))) = k3_lattices(esk6_0,X1,k4_lattices(esk6_0,X2,k7_lattices(esk6_0,esk8_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_56]),c_0_124]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_202,negated_conjecture,
    ( k4_lattices(esk6_0,k7_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0)),esk7_0) = esk7_0
    | k5_lattices(esk6_0) = k4_lattices(esk6_0,esk7_0,esk8_0)
    | ~ l2_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_187,c_0_188])])).

cnf(c_0_203,negated_conjecture,
    ( k3_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0),esk7_0) = esk7_0
    | ~ m1_subset_1(k7_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0)),u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189,c_0_190]),c_0_115]),c_0_146])).

cnf(c_0_204,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0)),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_188]),c_0_35])]),c_0_36])).

cnf(c_0_205,negated_conjecture,
    ( k4_lattices(esk6_0,k4_lattices(esk6_0,k3_lattices(esk6_0,X1,X2),k3_lattices(esk6_0,X2,esk8_0)),k3_lattices(esk6_0,esk8_0,X1)) = k3_lattices(esk6_0,k3_lattices(esk6_0,k4_lattices(esk6_0,X1,X2),k4_lattices(esk6_0,X2,esk8_0)),k4_lattices(esk6_0,esk8_0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_49]),c_0_34]),c_0_35])]),c_0_36]),c_0_124])])).

cnf(c_0_206,negated_conjecture,
    ( k3_lattices(esk6_0,esk8_0,k5_lattices(esk6_0)) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_193]),c_0_194]),c_0_195]),c_0_149]),c_0_56]),c_0_49])])).

cnf(c_0_207,negated_conjecture,
    ( k4_lattices(esk6_0,k5_lattices(esk6_0),esk7_0) = k5_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_43]),c_0_34]),c_0_35])]),c_0_36]),c_0_151])])).

cnf(c_0_208,negated_conjecture,
    ( k4_lattices(esk6_0,esk8_0,k5_lattices(esk6_0)) = k5_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_186]),c_0_49]),c_0_151]),c_0_34]),c_0_35]),c_0_137])]),c_0_36])).

cnf(c_0_209,negated_conjecture,
    ( k3_lattices(esk6_0,k5_lattices(esk6_0),k4_lattices(esk6_0,esk7_0,esk8_0)) = k4_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_196]),c_0_197]),c_0_43]),c_0_137])])).

cnf(c_0_210,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,k3_lattices(esk6_0,esk7_0,esk8_0)) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_157]),c_0_198]),c_0_157]),c_0_137]),c_0_43])])).

cnf(c_0_211,negated_conjecture,
    ( k3_lattices(esk6_0,X1,esk7_0) = k3_lattices(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199,c_0_87]),c_0_35])])).

cnf(c_0_212,negated_conjecture,
    ( k4_lattices(esk6_0,k6_lattices(esk6_0),k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk7_0)) = k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),k4_lattices(esk6_0,esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_102]),c_0_49]),c_0_56])]),c_0_167])).

cnf(c_0_213,negated_conjecture,
    ( k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk7_0) = k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189,c_0_200]),c_0_49])])).

cnf(c_0_214,negated_conjecture,
    ( k4_lattices(esk6_0,k6_lattices(esk6_0),k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0))) = k3_lattices(esk6_0,esk7_0,k4_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),k7_lattices(esk6_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201,c_0_140]),c_0_116]),c_0_43])])).

cnf(c_0_215,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_216,negated_conjecture,
    ( k4_lattices(esk6_0,k5_lattices(esk6_0),k7_lattices(esk6_0,esk8_0)) = k5_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_56]),c_0_151]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_217,negated_conjecture,
    ( k4_lattices(esk6_0,esk8_0,k6_lattices(esk6_0)) = esk8_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_186]),c_0_49]),c_0_127]),c_0_34]),c_0_35]),c_0_122])]),c_0_36])).

cnf(c_0_218,negated_conjecture,
    ( k4_lattices(esk6_0,k7_lattices(esk6_0,k4_lattices(esk6_0,X1,esk7_0)),k3_lattices(esk6_0,k7_lattices(esk6_0,X1),esk7_0)) = k3_lattices(esk6_0,k7_lattices(esk6_0,X1),k5_lattices(esk6_0))
    | ~ m1_subset_1(k7_lattices(esk6_0,X1),u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_114]),c_0_143]),c_0_116])])).

cnf(c_0_219,negated_conjecture,
    ( k4_lattices(esk6_0,k7_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0)),esk7_0) = esk7_0
    | k5_lattices(esk6_0) = k4_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_202,c_0_87]),c_0_35])])).

cnf(c_0_220,negated_conjecture,
    ( k3_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0),esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_203,c_0_204])])).

cnf(c_0_221,negated_conjecture,
    ( k3_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0),k5_lattices(esk6_0)) = k4_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205,c_0_196]),c_0_206]),c_0_207]),c_0_208]),c_0_43]),c_0_137])]),c_0_209]),c_0_210])).

cnf(c_0_222,negated_conjecture,
    ( k3_lattices(esk6_0,esk7_0,k6_lattices(esk6_0)) = k6_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_211]),c_0_43]),c_0_127]),c_0_34]),c_0_35]),c_0_122])]),c_0_36])).

cnf(c_0_223,negated_conjecture,
    ( k4_lattices(esk6_0,k6_lattices(esk6_0),k7_lattices(esk6_0,esk8_0)) = k7_lattices(esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_56]),c_0_127]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_224,negated_conjecture,
    ( k3_lattices(esk6_0,esk7_0,k4_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),k7_lattices(esk6_0,esk8_0))) = k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),k4_lattices(esk6_0,esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_212,c_0_213]),c_0_214])).

cnf(c_0_225,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,esk8_0) != k5_lattices(esk6_0)
    | ~ r3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_226,negated_conjecture,
    ( r3_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))
    | ~ r1_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_215,c_0_56]),c_0_44]),c_0_45]),c_0_46]),c_0_35])]),c_0_36])).

cnf(c_0_227,negated_conjecture,
    ( r1_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_131]),c_0_43]),c_0_45]),c_0_46]),c_0_35])]),c_0_36])).

cnf(c_0_228,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0))) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201,c_0_157]),c_0_216]),c_0_157]),c_0_137]),c_0_43])])).

cnf(c_0_229,negated_conjecture,
    ( k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),k5_lattices(esk6_0)) = k7_lattices(esk6_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_217]),c_0_49])])).

cnf(c_0_230,negated_conjecture,
    ( k5_lattices(esk6_0) = k4_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_218,c_0_219]),c_0_146]),c_0_220]),c_0_143]),c_0_146]),c_0_221]),c_0_146]),c_0_188]),c_0_204])])).

cnf(c_0_231,negated_conjecture,
    ( k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),k4_lattices(esk6_0,esk7_0,esk8_0)) = k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201,c_0_222]),c_0_223]),c_0_122]),c_0_43])]),c_0_214]),c_0_224])).

cnf(c_0_232,negated_conjecture,
    ( k5_lattices(esk6_0) != k4_lattices(esk6_0,esk7_0,esk8_0)
    | ~ r1_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_225,c_0_226]),c_0_43])])).

cnf(c_0_233,negated_conjecture,
    ( r1_lattices(esk6_0,esk7_0,k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)))
    | ~ m1_subset_1(k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_227,c_0_228])).

cnf(c_0_234,negated_conjecture,
    ( k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) = k7_lattices(esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_229,c_0_230]),c_0_231])).

cnf(c_0_235,negated_conjecture,
    ( ~ r1_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_232,c_0_230])])).

cnf(c_0_236,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_233,c_0_234]),c_0_234]),c_0_56])]),c_0_235]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 9.32/9.51  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 9.32/9.51  # and selection function PSelectComplexExceptUniqMaxHorn.
% 9.32/9.51  #
% 9.32/9.51  # Preprocessing time       : 0.032 s
% 9.32/9.51  
% 9.32/9.51  # Proof found!
% 9.32/9.51  # SZS status Theorem
% 9.32/9.51  # SZS output start CNFRefutation
% 9.32/9.51  fof(t52_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k4_lattices(X1,X2,X3)=k5_lattices(X1)<=>r3_lattices(X1,X2,k7_lattices(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_lattices)).
% 9.32/9.51  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 9.32/9.51  fof(t18_lattices, axiom, ![X1]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,X2,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_lattices)).
% 9.32/9.51  fof(dt_k7_lattices, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_lattices)).
% 9.32/9.51  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 9.32/9.51  fof(t23_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>r1_lattices(X1,k4_lattices(X1,X2,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_lattices)).
% 9.32/9.51  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 9.32/9.51  fof(d7_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v7_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>k2_lattices(X1,X2,k2_lattices(X1,X3,X4))=k2_lattices(X1,k2_lattices(X1,X2,X3),X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_lattices)).
% 9.32/9.51  fof(redefinition_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 9.32/9.51  fof(t49_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k7_lattices(X1,k7_lattices(X1,X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_lattices)).
% 9.32/9.51  fof(t51_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k7_lattices(X1,k3_lattices(X1,X2,X3))=k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_lattices)).
% 9.32/9.51  fof(t48_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k3_lattices(X1,k7_lattices(X1,X2),X2)=k6_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattices)).
% 9.32/9.51  fof(dt_k6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>m1_subset_1(k6_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_lattices)).
% 9.32/9.51  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 9.32/9.51  fof(t17_lattices, axiom, ![X1]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k1_lattices(X1,X2,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_lattices)).
% 9.32/9.51  fof(cc5_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v17_lattices(X1))=>(((~(v2_struct_0(X1))&v11_lattices(X1))&v15_lattices(X1))&v16_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_lattices)).
% 9.32/9.51  fof(t50_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k7_lattices(X1,k4_lattices(X1,X2,X3))=k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattices)).
% 9.32/9.51  fof(commutativity_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 9.32/9.51  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 9.32/9.51  fof(t47_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,k7_lattices(X1,X2),X2)=k5_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_lattices)).
% 9.32/9.51  fof(redefinition_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 9.32/9.51  fof(cc4_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v15_lattices(X1))=>((~(v2_struct_0(X1))&v13_lattices(X1))&v14_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_lattices)).
% 9.32/9.51  fof(t31_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>k3_lattices(X1,X2,k4_lattices(X1,X3,X4))=k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_lattices)).
% 9.32/9.51  fof(t43_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v14_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,k6_lattices(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_lattices)).
% 9.32/9.51  fof(commutativity_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 9.32/9.51  fof(t40_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,k5_lattices(X1),X2)=k5_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_lattices)).
% 9.32/9.51  fof(t44_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v14_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k3_lattices(X1,k6_lattices(X1),X2)=k6_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_lattices)).
% 9.32/9.51  fof(t39_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k3_lattices(X1,k5_lattices(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_lattices)).
% 9.32/9.51  fof(t34_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>k4_lattices(X1,k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X3,X4)),k3_lattices(X1,X4,X2))=k3_lattices(X1,k3_lattices(X1,k4_lattices(X1,X2,X3),k4_lattices(X1,X3,X4)),k4_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattices)).
% 9.32/9.51  fof(c_0_29, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k4_lattices(X1,X2,X3)=k5_lattices(X1)<=>r3_lattices(X1,X2,k7_lattices(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_lattices])).
% 9.32/9.51  fof(c_0_30, plain, ![X7]:(((((((~v2_struct_0(X7)|(v2_struct_0(X7)|~v10_lattices(X7))|~l3_lattices(X7))&(v4_lattices(X7)|(v2_struct_0(X7)|~v10_lattices(X7))|~l3_lattices(X7)))&(v5_lattices(X7)|(v2_struct_0(X7)|~v10_lattices(X7))|~l3_lattices(X7)))&(v6_lattices(X7)|(v2_struct_0(X7)|~v10_lattices(X7))|~l3_lattices(X7)))&(v7_lattices(X7)|(v2_struct_0(X7)|~v10_lattices(X7))|~l3_lattices(X7)))&(v8_lattices(X7)|(v2_struct_0(X7)|~v10_lattices(X7))|~l3_lattices(X7)))&(v9_lattices(X7)|(v2_struct_0(X7)|~v10_lattices(X7))|~l3_lattices(X7))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 9.32/9.51  fof(c_0_31, negated_conjecture, ((((~v2_struct_0(esk6_0)&v10_lattices(esk6_0))&v17_lattices(esk6_0))&l3_lattices(esk6_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&(m1_subset_1(esk8_0,u1_struct_0(esk6_0))&((k4_lattices(esk6_0,esk7_0,esk8_0)!=k5_lattices(esk6_0)|~r3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)))&(k4_lattices(esk6_0,esk7_0,esk8_0)=k5_lattices(esk6_0)|r3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_29])])])])).
% 9.32/9.51  fof(c_0_32, plain, ![X44, X45]:(v2_struct_0(X44)|~v6_lattices(X44)|~v8_lattices(X44)|~v9_lattices(X44)|~l3_lattices(X44)|(~m1_subset_1(X45,u1_struct_0(X44))|k4_lattices(X44,X45,X45)=X45)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t18_lattices])])])])).
% 9.32/9.51  cnf(c_0_33, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.32/9.51  cnf(c_0_34, negated_conjecture, (v10_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.32/9.51  cnf(c_0_35, negated_conjecture, (l3_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.32/9.51  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.32/9.51  cnf(c_0_37, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.32/9.51  cnf(c_0_38, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.32/9.51  fof(c_0_39, plain, ![X30, X31]:(v2_struct_0(X30)|~l3_lattices(X30)|~m1_subset_1(X31,u1_struct_0(X30))|m1_subset_1(k7_lattices(X30,X31),u1_struct_0(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).
% 9.32/9.51  fof(c_0_40, plain, ![X46, X47, X48]:((~r1_lattices(X46,X47,X48)|k2_lattices(X46,X47,X48)=X47|~m1_subset_1(X48,u1_struct_0(X46))|~m1_subset_1(X47,u1_struct_0(X46))|(v2_struct_0(X46)|~v8_lattices(X46)|~v9_lattices(X46)|~l3_lattices(X46)))&(k2_lattices(X46,X47,X48)!=X47|r1_lattices(X46,X47,X48)|~m1_subset_1(X48,u1_struct_0(X46))|~m1_subset_1(X47,u1_struct_0(X46))|(v2_struct_0(X46)|~v8_lattices(X46)|~v9_lattices(X46)|~l3_lattices(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 9.32/9.51  fof(c_0_41, plain, ![X52, X53, X54]:(v2_struct_0(X52)|~v6_lattices(X52)|~v8_lattices(X52)|~l3_lattices(X52)|(~m1_subset_1(X53,u1_struct_0(X52))|(~m1_subset_1(X54,u1_struct_0(X52))|r1_lattices(X52,k4_lattices(X52,X53,X54),X53)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_lattices])])])])).
% 9.32/9.51  cnf(c_0_42, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X2)=X2|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 9.32/9.51  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.32/9.51  cnf(c_0_44, negated_conjecture, (v9_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_45, negated_conjecture, (v8_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_46, negated_conjecture, (v6_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  fof(c_0_47, plain, ![X39, X40, X41]:((~r3_lattices(X39,X40,X41)|r1_lattices(X39,X40,X41)|(v2_struct_0(X39)|~v6_lattices(X39)|~v8_lattices(X39)|~v9_lattices(X39)|~l3_lattices(X39)|~m1_subset_1(X40,u1_struct_0(X39))|~m1_subset_1(X41,u1_struct_0(X39))))&(~r1_lattices(X39,X40,X41)|r3_lattices(X39,X40,X41)|(v2_struct_0(X39)|~v6_lattices(X39)|~v8_lattices(X39)|~v9_lattices(X39)|~l3_lattices(X39)|~m1_subset_1(X40,u1_struct_0(X39))|~m1_subset_1(X41,u1_struct_0(X39))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 9.32/9.51  cnf(c_0_48, plain, (v2_struct_0(X1)|m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 9.32/9.51  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.32/9.51  cnf(c_0_50, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 9.32/9.51  cnf(c_0_51, plain, (v2_struct_0(X1)|r1_lattices(X1,k4_lattices(X1,X2,X3),X2)|~v6_lattices(X1)|~v8_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 9.32/9.51  cnf(c_0_52, negated_conjecture, (k4_lattices(esk6_0,esk7_0,esk7_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_35])]), c_0_36]), c_0_44]), c_0_45]), c_0_46])])).
% 9.32/9.51  fof(c_0_53, plain, ![X16, X17, X18, X19]:((~v7_lattices(X16)|(~m1_subset_1(X17,u1_struct_0(X16))|(~m1_subset_1(X18,u1_struct_0(X16))|(~m1_subset_1(X19,u1_struct_0(X16))|k2_lattices(X16,X17,k2_lattices(X16,X18,X19))=k2_lattices(X16,k2_lattices(X16,X17,X18),X19))))|(v2_struct_0(X16)|~l1_lattices(X16)))&((m1_subset_1(esk1_1(X16),u1_struct_0(X16))|v7_lattices(X16)|(v2_struct_0(X16)|~l1_lattices(X16)))&((m1_subset_1(esk2_1(X16),u1_struct_0(X16))|v7_lattices(X16)|(v2_struct_0(X16)|~l1_lattices(X16)))&((m1_subset_1(esk3_1(X16),u1_struct_0(X16))|v7_lattices(X16)|(v2_struct_0(X16)|~l1_lattices(X16)))&(k2_lattices(X16,esk1_1(X16),k2_lattices(X16,esk2_1(X16),esk3_1(X16)))!=k2_lattices(X16,k2_lattices(X16,esk1_1(X16),esk2_1(X16)),esk3_1(X16))|v7_lattices(X16)|(v2_struct_0(X16)|~l1_lattices(X16))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_lattices])])])])])])).
% 9.32/9.51  cnf(c_0_54, plain, (v7_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.32/9.51  cnf(c_0_55, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 9.32/9.51  cnf(c_0_56, negated_conjecture, (m1_subset_1(k7_lattices(esk6_0,esk8_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_57, negated_conjecture, (k2_lattices(esk6_0,X1,esk7_0)=X1|~r1_lattices(esk6_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_43]), c_0_35])]), c_0_36]), c_0_44]), c_0_45])])).
% 9.32/9.51  cnf(c_0_58, negated_conjecture, (r1_lattices(esk6_0,esk7_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_43]), c_0_45]), c_0_46]), c_0_35])]), c_0_36])).
% 9.32/9.51  fof(c_0_59, plain, ![X36, X37, X38]:(v2_struct_0(X36)|~v6_lattices(X36)|~l1_lattices(X36)|~m1_subset_1(X37,u1_struct_0(X36))|~m1_subset_1(X38,u1_struct_0(X36))|k4_lattices(X36,X37,X38)=k2_lattices(X36,X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).
% 9.32/9.51  cnf(c_0_60, plain, (k2_lattices(X1,X2,k2_lattices(X1,X3,X4))=k2_lattices(X1,k2_lattices(X1,X2,X3),X4)|v2_struct_0(X1)|~v7_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 9.32/9.51  cnf(c_0_61, negated_conjecture, (v7_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  fof(c_0_62, plain, ![X79, X80]:(v2_struct_0(X79)|~v10_lattices(X79)|~v17_lattices(X79)|~l3_lattices(X79)|(~m1_subset_1(X80,u1_struct_0(X79))|k7_lattices(X79,k7_lattices(X79,X80))=X80)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_lattices])])])])).
% 9.32/9.51  cnf(c_0_63, negated_conjecture, (r1_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))|~r3_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_44]), c_0_45]), c_0_46]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_64, negated_conjecture, (k4_lattices(esk6_0,esk7_0,esk8_0)=k5_lattices(esk6_0)|r3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.32/9.51  cnf(c_0_65, negated_conjecture, (k2_lattices(esk6_0,esk7_0,esk7_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_43])])).
% 9.32/9.51  cnf(c_0_66, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 9.32/9.51  cnf(c_0_67, negated_conjecture, (k2_lattices(esk6_0,k2_lattices(esk6_0,X1,X2),esk8_0)=k2_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,esk8_0))|~l1_lattices(esk6_0)|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_49]), c_0_36]), c_0_61])])).
% 9.32/9.51  fof(c_0_68, plain, ![X84, X85, X86]:(v2_struct_0(X84)|~v10_lattices(X84)|~v17_lattices(X84)|~l3_lattices(X84)|(~m1_subset_1(X85,u1_struct_0(X84))|(~m1_subset_1(X86,u1_struct_0(X84))|k7_lattices(X84,k3_lattices(X84,X85,X86))=k4_lattices(X84,k7_lattices(X84,X85),k7_lattices(X84,X86))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t51_lattices])])])])).
% 9.32/9.51  fof(c_0_69, plain, ![X77, X78]:(v2_struct_0(X77)|~v10_lattices(X77)|~v17_lattices(X77)|~l3_lattices(X77)|(~m1_subset_1(X78,u1_struct_0(X77))|k3_lattices(X77,k7_lattices(X77,X78),X78)=k6_lattices(X77))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattices])])])])).
% 9.32/9.51  fof(c_0_70, plain, ![X29]:(v2_struct_0(X29)|~l2_lattices(X29)|m1_subset_1(k6_lattices(X29),u1_struct_0(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_lattices])])])).
% 9.32/9.51  fof(c_0_71, plain, ![X32]:((l1_lattices(X32)|~l3_lattices(X32))&(l2_lattices(X32)|~l3_lattices(X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 9.32/9.51  fof(c_0_72, plain, ![X42, X43]:(v2_struct_0(X42)|~v6_lattices(X42)|~v8_lattices(X42)|~v9_lattices(X42)|~l3_lattices(X42)|(~m1_subset_1(X43,u1_struct_0(X42))|k1_lattices(X42,X43,X43)=X43)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_lattices])])])])).
% 9.32/9.51  fof(c_0_73, plain, ![X9]:((((~v2_struct_0(X9)|(v2_struct_0(X9)|~v17_lattices(X9))|~l3_lattices(X9))&(v11_lattices(X9)|(v2_struct_0(X9)|~v17_lattices(X9))|~l3_lattices(X9)))&(v15_lattices(X9)|(v2_struct_0(X9)|~v17_lattices(X9))|~l3_lattices(X9)))&(v16_lattices(X9)|(v2_struct_0(X9)|~v17_lattices(X9))|~l3_lattices(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_lattices])])])])).
% 9.32/9.51  cnf(c_0_74, plain, (v2_struct_0(X1)|k7_lattices(X1,k7_lattices(X1,X2))=X2|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 9.32/9.51  cnf(c_0_75, negated_conjecture, (v17_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.32/9.51  fof(c_0_76, plain, ![X81, X82, X83]:(v2_struct_0(X81)|~v10_lattices(X81)|~v17_lattices(X81)|~l3_lattices(X81)|(~m1_subset_1(X82,u1_struct_0(X81))|(~m1_subset_1(X83,u1_struct_0(X81))|k7_lattices(X81,k4_lattices(X81,X82,X83))=k3_lattices(X81,k7_lattices(X81,X82),k7_lattices(X81,X83))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_lattices])])])])).
% 9.32/9.51  fof(c_0_77, plain, ![X13, X14, X15]:(v2_struct_0(X13)|~v6_lattices(X13)|~l1_lattices(X13)|~m1_subset_1(X14,u1_struct_0(X13))|~m1_subset_1(X15,u1_struct_0(X13))|k4_lattices(X13,X14,X15)=k4_lattices(X13,X15,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).
% 9.32/9.51  cnf(c_0_78, negated_conjecture, (k2_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))=X1|~r1_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_56]), c_0_44]), c_0_45]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_79, negated_conjecture, (k5_lattices(esk6_0)=k4_lattices(esk6_0,esk7_0,esk8_0)|r1_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_43])])).
% 9.32/9.51  cnf(c_0_80, negated_conjecture, (k2_lattices(esk6_0,esk7_0,k2_lattices(esk6_0,esk7_0,X1))=k2_lattices(esk6_0,esk7_0,X1)|~l1_lattices(esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_65]), c_0_43]), c_0_61])]), c_0_36])).
% 9.32/9.51  cnf(c_0_81, negated_conjecture, (k2_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,esk8_0))=k4_lattices(esk6_0,k2_lattices(esk6_0,X1,X2),esk8_0)|~l1_lattices(esk6_0)|~m1_subset_1(k2_lattices(esk6_0,X1,X2),u1_struct_0(esk6_0))|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_49]), c_0_46])]), c_0_36])).
% 9.32/9.51  fof(c_0_82, plain, ![X28]:(v2_struct_0(X28)|~l1_lattices(X28)|m1_subset_1(k5_lattices(X28),u1_struct_0(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 9.32/9.51  fof(c_0_83, plain, ![X75, X76]:(v2_struct_0(X75)|~v10_lattices(X75)|~v17_lattices(X75)|~l3_lattices(X75)|(~m1_subset_1(X76,u1_struct_0(X75))|k4_lattices(X75,k7_lattices(X75,X76),X76)=k5_lattices(X75))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattices])])])])).
% 9.32/9.51  cnf(c_0_84, plain, (v2_struct_0(X1)|k7_lattices(X1,k3_lattices(X1,X2,X3))=k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 9.32/9.51  cnf(c_0_85, plain, (v2_struct_0(X1)|k3_lattices(X1,k7_lattices(X1,X2),X2)=k6_lattices(X1)|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 9.32/9.51  cnf(c_0_86, plain, (v2_struct_0(X1)|m1_subset_1(k6_lattices(X1),u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 9.32/9.51  cnf(c_0_87, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 9.32/9.51  fof(c_0_88, plain, ![X33, X34, X35]:(v2_struct_0(X33)|~v4_lattices(X33)|~l2_lattices(X33)|~m1_subset_1(X34,u1_struct_0(X33))|~m1_subset_1(X35,u1_struct_0(X33))|k3_lattices(X33,X34,X35)=k1_lattices(X33,X34,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).
% 9.32/9.51  cnf(c_0_89, plain, (v2_struct_0(X1)|k1_lattices(X1,X2,X2)=X2|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 9.32/9.51  cnf(c_0_90, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.32/9.51  fof(c_0_91, plain, ![X8]:(((~v2_struct_0(X8)|(v2_struct_0(X8)|~v15_lattices(X8))|~l3_lattices(X8))&(v13_lattices(X8)|(v2_struct_0(X8)|~v15_lattices(X8))|~l3_lattices(X8)))&(v14_lattices(X8)|(v2_struct_0(X8)|~v15_lattices(X8))|~l3_lattices(X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_lattices])])])])).
% 9.32/9.51  cnf(c_0_92, plain, (v15_lattices(X1)|v2_struct_0(X1)|~v17_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 9.32/9.51  cnf(c_0_93, negated_conjecture, (k7_lattices(esk6_0,k7_lattices(esk6_0,esk8_0))=esk8_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_49]), c_0_75]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_94, plain, (v2_struct_0(X1)|k7_lattices(X1,k4_lattices(X1,X2,X3))=k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 9.32/9.51  cnf(c_0_95, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 9.32/9.51  cnf(c_0_96, negated_conjecture, (k2_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0))=esk7_0|k5_lattices(esk6_0)=k4_lattices(esk6_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_43])])).
% 9.32/9.51  cnf(c_0_97, negated_conjecture, (k2_lattices(esk6_0,esk7_0,esk8_0)=k4_lattices(esk6_0,esk7_0,esk8_0)|~l1_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_65]), c_0_49]), c_0_65]), c_0_43]), c_0_43])])).
% 9.32/9.51  cnf(c_0_98, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 9.32/9.51  cnf(c_0_99, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 9.32/9.51  cnf(c_0_100, plain, (v2_struct_0(X1)|k4_lattices(X1,k7_lattices(X1,X2),X2)=k5_lattices(X1)|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 9.32/9.51  cnf(c_0_101, negated_conjecture, (k4_lattices(esk6_0,k7_lattices(esk6_0,X1),k7_lattices(esk6_0,esk8_0))=k7_lattices(esk6_0,k3_lattices(esk6_0,X1,esk8_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_49]), c_0_75]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_102, negated_conjecture, (k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk8_0)=k6_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_49]), c_0_75]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_103, plain, (m1_subset_1(k6_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 9.32/9.51  fof(c_0_104, plain, ![X59, X60, X61, X62]:(v2_struct_0(X59)|~v10_lattices(X59)|~v11_lattices(X59)|~l3_lattices(X59)|(~m1_subset_1(X60,u1_struct_0(X59))|(~m1_subset_1(X61,u1_struct_0(X59))|(~m1_subset_1(X62,u1_struct_0(X59))|k3_lattices(X59,X60,k4_lattices(X59,X61,X62))=k4_lattices(X59,k3_lattices(X59,X60,X61),k3_lattices(X59,X60,X62)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_lattices])])])])).
% 9.32/9.51  cnf(c_0_105, plain, (v11_lattices(X1)|v2_struct_0(X1)|~v17_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 9.32/9.51  cnf(c_0_106, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 9.32/9.51  cnf(c_0_107, negated_conjecture, (k1_lattices(esk6_0,esk7_0,esk7_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_43]), c_0_35])]), c_0_36]), c_0_44]), c_0_45]), c_0_46])])).
% 9.32/9.51  cnf(c_0_108, negated_conjecture, (v4_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  fof(c_0_109, plain, ![X71, X72]:(v2_struct_0(X71)|~v10_lattices(X71)|~v14_lattices(X71)|~l3_lattices(X71)|(~m1_subset_1(X72,u1_struct_0(X71))|k4_lattices(X71,k6_lattices(X71),X72)=X72)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_lattices])])])])).
% 9.32/9.51  cnf(c_0_110, plain, (v14_lattices(X1)|v2_struct_0(X1)|~v15_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 9.32/9.51  cnf(c_0_111, negated_conjecture, (v15_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_75]), c_0_35])]), c_0_36])).
% 9.32/9.51  fof(c_0_112, plain, ![X10, X11, X12]:(v2_struct_0(X10)|~v4_lattices(X10)|~l2_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))|k3_lattices(X10,X11,X12)=k3_lattices(X10,X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).
% 9.32/9.51  cnf(c_0_113, negated_conjecture, (k7_lattices(esk6_0,k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),X1))=k4_lattices(esk6_0,esk8_0,k7_lattices(esk6_0,X1))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_93]), c_0_56]), c_0_75]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_114, negated_conjecture, (k3_lattices(esk6_0,k7_lattices(esk6_0,X1),k7_lattices(esk6_0,esk7_0))=k7_lattices(esk6_0,k4_lattices(esk6_0,X1,esk7_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_43]), c_0_75]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_115, negated_conjecture, (k7_lattices(esk6_0,k7_lattices(esk6_0,esk7_0))=esk7_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_43]), c_0_75]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_116, negated_conjecture, (m1_subset_1(k7_lattices(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_43]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_117, negated_conjecture, (k4_lattices(esk6_0,X1,esk7_0)=k4_lattices(esk6_0,esk7_0,X1)|~l1_lattices(esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_43]), c_0_36]), c_0_46])])).
% 9.32/9.51  cnf(c_0_118, negated_conjecture, (k2_lattices(esk6_0,esk7_0,k2_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk8_0))=k2_lattices(esk6_0,esk7_0,esk8_0)|k5_lattices(esk6_0)=k4_lattices(esk6_0,esk7_0,esk8_0)|~l1_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_96]), c_0_56]), c_0_43])])).
% 9.32/9.51  cnf(c_0_119, negated_conjecture, (k2_lattices(esk6_0,esk7_0,esk8_0)=k4_lattices(esk6_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_35])])).
% 9.32/9.51  cnf(c_0_120, plain, (m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_99, c_0_98])).
% 9.32/9.51  cnf(c_0_121, negated_conjecture, (k7_lattices(esk6_0,k6_lattices(esk6_0))=k5_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102]), c_0_56]), c_0_75]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_122, negated_conjecture, (m1_subset_1(k6_lattices(esk6_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_35]), c_0_36])).
% 9.32/9.51  cnf(c_0_123, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,k4_lattices(X1,X3,X4))=k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X2,X4))|~v10_lattices(X1)|~v11_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_104])).
% 9.32/9.51  cnf(c_0_124, negated_conjecture, (v11_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_75]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_125, negated_conjecture, (k3_lattices(esk6_0,esk7_0,esk7_0)=esk7_0|~l2_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_43]), c_0_108])]), c_0_36])).
% 9.32/9.51  cnf(c_0_126, plain, (v2_struct_0(X1)|k4_lattices(X1,k6_lattices(X1),X2)=X2|~v10_lattices(X1)|~v14_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_109])).
% 9.32/9.51  cnf(c_0_127, negated_conjecture, (v14_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_128, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_112])).
% 9.32/9.51  cnf(c_0_129, negated_conjecture, (k3_lattices(esk6_0,k7_lattices(esk6_0,X1),k7_lattices(esk6_0,esk8_0))=k7_lattices(esk6_0,k4_lattices(esk6_0,X1,esk8_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_49]), c_0_75]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_130, negated_conjecture, (k7_lattices(esk6_0,k7_lattices(esk6_0,k4_lattices(esk6_0,esk8_0,esk7_0)))=k4_lattices(esk6_0,esk8_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115]), c_0_116]), c_0_49])])).
% 9.32/9.51  cnf(c_0_131, negated_conjecture, (k4_lattices(esk6_0,X1,esk7_0)=k4_lattices(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_98]), c_0_35])])).
% 9.32/9.51  cnf(c_0_132, negated_conjecture, (k2_lattices(esk6_0,esk7_0,k2_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk8_0))=k4_lattices(esk6_0,esk7_0,esk8_0)|k5_lattices(esk6_0)=k4_lattices(esk6_0,esk7_0,esk8_0)|~l1_lattices(esk6_0)), inference(rw,[status(thm)],[c_0_118, c_0_119])).
% 9.32/9.51  cnf(c_0_133, negated_conjecture, (k2_lattices(esk6_0,X1,esk8_0)=k4_lattices(esk6_0,X1,esk8_0)|~l1_lattices(esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_49]), c_0_36]), c_0_46])])).
% 9.32/9.51  fof(c_0_134, plain, ![X69, X70]:(v2_struct_0(X69)|~v10_lattices(X69)|~v13_lattices(X69)|~l3_lattices(X69)|(~m1_subset_1(X70,u1_struct_0(X69))|k4_lattices(X69,k5_lattices(X69),X70)=k5_lattices(X69))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_lattices])])])])).
% 9.32/9.51  cnf(c_0_135, plain, (v13_lattices(X1)|v2_struct_0(X1)|~v15_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 9.32/9.51  cnf(c_0_136, negated_conjecture, (k4_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0))=esk7_0|k5_lattices(esk6_0)=k4_lattices(esk6_0,esk7_0,esk8_0)|~l1_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_96]), c_0_56]), c_0_43]), c_0_46])]), c_0_36])).
% 9.32/9.51  cnf(c_0_137, negated_conjecture, (m1_subset_1(k5_lattices(esk6_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_35]), c_0_36])).
% 9.32/9.51  cnf(c_0_138, negated_conjecture, (k7_lattices(esk6_0,k5_lattices(esk6_0))=k6_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_121]), c_0_122]), c_0_75]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_139, negated_conjecture, (k4_lattices(esk6_0,k3_lattices(esk6_0,X1,X2),k3_lattices(esk6_0,X1,esk7_0))=k3_lattices(esk6_0,X1,k4_lattices(esk6_0,X2,esk7_0))|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_43]), c_0_34]), c_0_35])]), c_0_36]), c_0_124])])).
% 9.32/9.51  cnf(c_0_140, negated_conjecture, (k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk7_0))=k6_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_115]), c_0_116]), c_0_75]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_141, negated_conjecture, (k3_lattices(esk6_0,esk7_0,esk7_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_87]), c_0_35])])).
% 9.32/9.51  cnf(c_0_142, negated_conjecture, (k4_lattices(esk6_0,k6_lattices(esk6_0),esk7_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_43]), c_0_34]), c_0_35])]), c_0_36]), c_0_127])])).
% 9.32/9.51  cnf(c_0_143, negated_conjecture, (k4_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),esk7_0)=k5_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_43]), c_0_75]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_144, negated_conjecture, (k7_lattices(esk6_0,k3_lattices(esk6_0,X1,k7_lattices(esk6_0,esk7_0)))=k4_lattices(esk6_0,k7_lattices(esk6_0,X1),esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_116]), c_0_75]), c_0_34]), c_0_35])]), c_0_36]), c_0_115])).
% 9.32/9.51  cnf(c_0_145, negated_conjecture, (k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),k7_lattices(esk6_0,X1))=k7_lattices(esk6_0,k4_lattices(esk6_0,X1,esk8_0))|~m1_subset_1(k7_lattices(esk6_0,X1),u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))|~l2_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_56]), c_0_108])]), c_0_36])).
% 9.32/9.51  cnf(c_0_146, negated_conjecture, (k7_lattices(esk6_0,k7_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0)))=k4_lattices(esk6_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_49])])).
% 9.32/9.51  cnf(c_0_147, negated_conjecture, (k2_lattices(esk6_0,esk7_0,k2_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk8_0))=k4_lattices(esk6_0,esk7_0,esk8_0)|k5_lattices(esk6_0)=k4_lattices(esk6_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_98]), c_0_35])])).
% 9.32/9.51  cnf(c_0_148, negated_conjecture, (k2_lattices(esk6_0,X1,esk8_0)=k4_lattices(esk6_0,X1,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_98]), c_0_35])])).
% 9.32/9.51  cnf(c_0_149, negated_conjecture, (k4_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk8_0)=k5_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_49]), c_0_75]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_150, plain, (v2_struct_0(X1)|k4_lattices(X1,k5_lattices(X1),X2)=k5_lattices(X1)|~v10_lattices(X1)|~v13_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_134])).
% 9.32/9.51  cnf(c_0_151, negated_conjecture, (v13_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_111]), c_0_35])]), c_0_36])).
% 9.32/9.51  fof(c_0_152, plain, ![X73, X74]:(v2_struct_0(X73)|~v10_lattices(X73)|~v14_lattices(X73)|~l3_lattices(X73)|(~m1_subset_1(X74,u1_struct_0(X73))|k3_lattices(X73,k6_lattices(X73),X74)=k6_lattices(X73))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_lattices])])])])).
% 9.32/9.51  cnf(c_0_153, negated_conjecture, (k3_lattices(esk6_0,X1,esk8_0)=k3_lattices(esk6_0,esk8_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~l2_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_49]), c_0_36]), c_0_108])])).
% 9.32/9.51  cnf(c_0_154, negated_conjecture, (k7_lattices(esk6_0,k4_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0)))=k3_lattices(esk6_0,k7_lattices(esk6_0,X1),esk8_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_56]), c_0_75]), c_0_34]), c_0_35])]), c_0_36]), c_0_93])).
% 9.32/9.51  cnf(c_0_155, negated_conjecture, (k4_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0))=esk7_0|k5_lattices(esk6_0)=k4_lattices(esk6_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_98]), c_0_35])])).
% 9.32/9.51  cnf(c_0_156, negated_conjecture, (k7_lattices(esk6_0,k3_lattices(esk6_0,X1,k5_lattices(esk6_0)))=k4_lattices(esk6_0,k7_lattices(esk6_0,X1),k6_lattices(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_137]), c_0_75]), c_0_34]), c_0_35])]), c_0_36]), c_0_138])).
% 9.32/9.51  cnf(c_0_157, negated_conjecture, (k3_lattices(esk6_0,esk7_0,k5_lattices(esk6_0))=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_141]), c_0_142]), c_0_143]), c_0_116]), c_0_43])])).
% 9.32/9.51  cnf(c_0_158, negated_conjecture, (k4_lattices(esk6_0,esk8_0,esk7_0)=k4_lattices(esk6_0,esk7_0,esk8_0)|~l2_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_145]), c_0_146]), c_0_93]), c_0_56]), c_0_116]), c_0_43])])).
% 9.32/9.51  cnf(c_0_159, negated_conjecture, (k2_lattices(esk6_0,esk7_0,k5_lattices(esk6_0))=k4_lattices(esk6_0,esk7_0,esk8_0)|k5_lattices(esk6_0)=k4_lattices(esk6_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_148]), c_0_149]), c_0_56])])).
% 9.32/9.51  cnf(c_0_160, negated_conjecture, (k4_lattices(esk6_0,esk7_0,k5_lattices(esk6_0))=k5_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_131]), c_0_43]), c_0_151]), c_0_34]), c_0_35]), c_0_137])]), c_0_36])).
% 9.32/9.51  cnf(c_0_161, plain, (v2_struct_0(X1)|k3_lattices(X1,k6_lattices(X1),X2)=k6_lattices(X1)|~v10_lattices(X1)|~v14_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_152])).
% 9.32/9.51  cnf(c_0_162, negated_conjecture, (k3_lattices(esk6_0,X1,esk8_0)=k3_lattices(esk6_0,esk8_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_87]), c_0_35])])).
% 9.32/9.51  cnf(c_0_163, negated_conjecture, (k3_lattices(esk6_0,X1,k7_lattices(esk6_0,esk7_0))=k3_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~l2_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_116]), c_0_108])]), c_0_36])).
% 9.32/9.51  cnf(c_0_164, negated_conjecture, (k3_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),esk8_0)=k7_lattices(esk6_0,esk7_0)|k5_lattices(esk6_0)=k4_lattices(esk6_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_155]), c_0_43])])).
% 9.32/9.51  cnf(c_0_165, negated_conjecture, (k3_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),esk7_0)=k6_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_43]), c_0_75]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_166, negated_conjecture, (k4_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),k6_lattices(esk6_0))=k7_lattices(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_157]), c_0_43])])).
% 9.32/9.51  cnf(c_0_167, negated_conjecture, (k4_lattices(esk6_0,esk8_0,esk7_0)=k4_lattices(esk6_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158, c_0_87]), c_0_35])])).
% 9.32/9.51  cnf(c_0_168, negated_conjecture, (k5_lattices(esk6_0)=k4_lattices(esk6_0,esk7_0,esk8_0)|~l1_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_159]), c_0_160]), c_0_137]), c_0_43]), c_0_46])]), c_0_36])).
% 9.32/9.51  cnf(c_0_169, negated_conjecture, (k7_lattices(esk6_0,k4_lattices(esk6_0,X1,k6_lattices(esk6_0)))=k3_lattices(esk6_0,k7_lattices(esk6_0,X1),k5_lattices(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_122]), c_0_75]), c_0_34]), c_0_35])]), c_0_36]), c_0_121])).
% 9.32/9.51  cnf(c_0_170, negated_conjecture, (k4_lattices(esk6_0,esk7_0,k6_lattices(esk6_0))=esk7_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_131]), c_0_43]), c_0_127]), c_0_34]), c_0_35]), c_0_122])]), c_0_36])).
% 9.32/9.51  cnf(c_0_171, negated_conjecture, (k7_lattices(esk6_0,k3_lattices(esk6_0,X1,k6_lattices(esk6_0)))=k4_lattices(esk6_0,k7_lattices(esk6_0,X1),k5_lattices(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_122]), c_0_75]), c_0_34]), c_0_35])]), c_0_36]), c_0_121])).
% 9.32/9.51  cnf(c_0_172, negated_conjecture, (k3_lattices(esk6_0,esk8_0,k6_lattices(esk6_0))=k6_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_162]), c_0_49]), c_0_127]), c_0_34]), c_0_35]), c_0_122])]), c_0_36])).
% 9.32/9.51  cnf(c_0_173, negated_conjecture, (k1_lattices(esk6_0,esk8_0,esk8_0)=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_49]), c_0_35])]), c_0_36]), c_0_44]), c_0_45]), c_0_46])])).
% 9.32/9.51  fof(c_0_174, plain, ![X67, X68]:(v2_struct_0(X67)|~v10_lattices(X67)|~v13_lattices(X67)|~l3_lattices(X67)|(~m1_subset_1(X68,u1_struct_0(X67))|k3_lattices(X67,k5_lattices(X67),X68)=X68)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_lattices])])])])).
% 9.32/9.51  cnf(c_0_175, negated_conjecture, (k4_lattices(esk6_0,X1,esk8_0)=k4_lattices(esk6_0,esk8_0,X1)|~l1_lattices(esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_49]), c_0_36]), c_0_46])])).
% 9.32/9.51  cnf(c_0_176, negated_conjecture, (k7_lattices(esk6_0,k3_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),X1))=k4_lattices(esk6_0,k7_lattices(esk6_0,X1),esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~l2_lattices(esk6_0)), inference(spm,[status(thm)],[c_0_144, c_0_163])).
% 9.32/9.51  cnf(c_0_177, negated_conjecture, (k3_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),k4_lattices(esk6_0,esk7_0,esk8_0))=k7_lattices(esk6_0,esk7_0)|k5_lattices(esk6_0)=k4_lattices(esk6_0,esk7_0,esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_164]), c_0_165]), c_0_49]), c_0_116])]), c_0_166]), c_0_167])).
% 9.32/9.51  cnf(c_0_178, negated_conjecture, (m1_subset_1(k4_lattices(esk6_0,esk7_0,esk8_0),u1_struct_0(esk6_0))|~l1_lattices(esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_168]), c_0_36])).
% 9.32/9.51  cnf(c_0_179, negated_conjecture, (k4_lattices(esk6_0,k7_lattices(esk6_0,k4_lattices(esk6_0,X1,esk8_0)),k3_lattices(esk6_0,k7_lattices(esk6_0,X1),X2))=k3_lattices(esk6_0,k7_lattices(esk6_0,X1),k4_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),X2))|~m1_subset_1(k7_lattices(esk6_0,X1),u1_struct_0(esk6_0))|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_129]), c_0_56]), c_0_124]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_180, negated_conjecture, (k3_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),k5_lattices(esk6_0))=k7_lattices(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_170]), c_0_43])])).
% 9.32/9.51  cnf(c_0_181, negated_conjecture, (k4_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),k5_lattices(esk6_0))=k5_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_172]), c_0_121]), c_0_49])])).
% 9.32/9.51  fof(c_0_182, plain, ![X63, X64, X65, X66]:(v2_struct_0(X63)|~v10_lattices(X63)|~v11_lattices(X63)|~l3_lattices(X63)|(~m1_subset_1(X64,u1_struct_0(X63))|(~m1_subset_1(X65,u1_struct_0(X63))|(~m1_subset_1(X66,u1_struct_0(X63))|k4_lattices(X63,k4_lattices(X63,k3_lattices(X63,X64,X65),k3_lattices(X63,X65,X66)),k3_lattices(X63,X66,X64))=k3_lattices(X63,k3_lattices(X63,k4_lattices(X63,X64,X65),k4_lattices(X63,X65,X66)),k4_lattices(X63,X66,X64)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattices])])])])).
% 9.32/9.51  cnf(c_0_183, negated_conjecture, (k3_lattices(esk6_0,esk8_0,esk8_0)=esk8_0|~l2_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_173]), c_0_49]), c_0_108])]), c_0_36])).
% 9.32/9.51  cnf(c_0_184, plain, (v2_struct_0(X1)|k3_lattices(X1,k5_lattices(X1),X2)=X2|~v10_lattices(X1)|~v13_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_174])).
% 9.32/9.51  cnf(c_0_185, negated_conjecture, (k7_lattices(esk6_0,k4_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),X1))=k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,X1))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_115]), c_0_116]), c_0_75]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_186, negated_conjecture, (k4_lattices(esk6_0,X1,esk8_0)=k4_lattices(esk6_0,esk8_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175, c_0_98]), c_0_35])])).
% 9.32/9.51  cnf(c_0_187, negated_conjecture, (k4_lattices(esk6_0,k7_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0)),esk7_0)=esk7_0|k5_lattices(esk6_0)=k4_lattices(esk6_0,esk7_0,esk8_0)|~m1_subset_1(k4_lattices(esk6_0,esk7_0,esk8_0),u1_struct_0(esk6_0))|~l2_lattices(esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176, c_0_177]), c_0_115])).
% 9.32/9.51  cnf(c_0_188, negated_conjecture, (m1_subset_1(k4_lattices(esk6_0,esk7_0,esk8_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178, c_0_98]), c_0_35])])).
% 9.32/9.51  cnf(c_0_189, negated_conjecture, (k7_lattices(esk6_0,k4_lattices(esk6_0,X1,k7_lattices(esk6_0,esk7_0)))=k3_lattices(esk6_0,k7_lattices(esk6_0,X1),esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_116]), c_0_75]), c_0_34]), c_0_35])]), c_0_36]), c_0_115])).
% 9.32/9.51  cnf(c_0_190, negated_conjecture, (k4_lattices(esk6_0,k7_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0)),k7_lattices(esk6_0,esk7_0))=k7_lattices(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179, c_0_180]), c_0_181]), c_0_180]), c_0_116]), c_0_137]), c_0_43])])).
% 9.32/9.51  cnf(c_0_191, plain, (v2_struct_0(X1)|k4_lattices(X1,k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X3,X4)),k3_lattices(X1,X4,X2))=k3_lattices(X1,k3_lattices(X1,k4_lattices(X1,X2,X3),k4_lattices(X1,X3,X4)),k4_lattices(X1,X4,X2))|~v10_lattices(X1)|~v11_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_182])).
% 9.32/9.51  cnf(c_0_192, negated_conjecture, (k4_lattices(esk6_0,k3_lattices(esk6_0,X1,X2),k3_lattices(esk6_0,X1,esk8_0))=k3_lattices(esk6_0,X1,k4_lattices(esk6_0,X2,esk8_0))|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_49]), c_0_34]), c_0_35])]), c_0_36]), c_0_124])])).
% 9.32/9.51  cnf(c_0_193, negated_conjecture, (k3_lattices(esk6_0,esk8_0,k7_lattices(esk6_0,esk8_0))=k6_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_93]), c_0_56]), c_0_75]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_194, negated_conjecture, (k3_lattices(esk6_0,esk8_0,esk8_0)=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183, c_0_87]), c_0_35])])).
% 9.32/9.51  cnf(c_0_195, negated_conjecture, (k4_lattices(esk6_0,k6_lattices(esk6_0),esk8_0)=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_49]), c_0_34]), c_0_35])]), c_0_36]), c_0_127])])).
% 9.32/9.51  cnf(c_0_196, negated_conjecture, (k3_lattices(esk6_0,k5_lattices(esk6_0),esk7_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184, c_0_43]), c_0_34]), c_0_35])]), c_0_36]), c_0_151])])).
% 9.32/9.51  cnf(c_0_197, negated_conjecture, (k3_lattices(esk6_0,k5_lattices(esk6_0),esk8_0)=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184, c_0_49]), c_0_34]), c_0_35])]), c_0_36]), c_0_151])])).
% 9.32/9.51  cnf(c_0_198, negated_conjecture, (k4_lattices(esk6_0,k5_lattices(esk6_0),esk8_0)=k5_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_49]), c_0_34]), c_0_35])]), c_0_36]), c_0_151])])).
% 9.32/9.51  cnf(c_0_199, negated_conjecture, (k3_lattices(esk6_0,X1,esk7_0)=k3_lattices(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~l2_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_43]), c_0_36]), c_0_108])])).
% 9.32/9.51  cnf(c_0_200, negated_conjecture, (k7_lattices(esk6_0,k4_lattices(esk6_0,esk8_0,k7_lattices(esk6_0,esk7_0)))=k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185, c_0_186]), c_0_49]), c_0_116])])).
% 9.32/9.51  cnf(c_0_201, negated_conjecture, (k4_lattices(esk6_0,k3_lattices(esk6_0,X1,X2),k3_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0)))=k3_lattices(esk6_0,X1,k4_lattices(esk6_0,X2,k7_lattices(esk6_0,esk8_0)))|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_56]), c_0_124]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_202, negated_conjecture, (k4_lattices(esk6_0,k7_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0)),esk7_0)=esk7_0|k5_lattices(esk6_0)=k4_lattices(esk6_0,esk7_0,esk8_0)|~l2_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_187, c_0_188])])).
% 9.32/9.51  cnf(c_0_203, negated_conjecture, (k3_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0),esk7_0)=esk7_0|~m1_subset_1(k7_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0)),u1_struct_0(esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189, c_0_190]), c_0_115]), c_0_146])).
% 9.32/9.51  cnf(c_0_204, negated_conjecture, (m1_subset_1(k7_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0)),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_188]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_205, negated_conjecture, (k4_lattices(esk6_0,k4_lattices(esk6_0,k3_lattices(esk6_0,X1,X2),k3_lattices(esk6_0,X2,esk8_0)),k3_lattices(esk6_0,esk8_0,X1))=k3_lattices(esk6_0,k3_lattices(esk6_0,k4_lattices(esk6_0,X1,X2),k4_lattices(esk6_0,X2,esk8_0)),k4_lattices(esk6_0,esk8_0,X1))|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_191, c_0_49]), c_0_34]), c_0_35])]), c_0_36]), c_0_124])])).
% 9.32/9.51  cnf(c_0_206, negated_conjecture, (k3_lattices(esk6_0,esk8_0,k5_lattices(esk6_0))=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192, c_0_193]), c_0_194]), c_0_195]), c_0_149]), c_0_56]), c_0_49])])).
% 9.32/9.51  cnf(c_0_207, negated_conjecture, (k4_lattices(esk6_0,k5_lattices(esk6_0),esk7_0)=k5_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_43]), c_0_34]), c_0_35])]), c_0_36]), c_0_151])])).
% 9.32/9.51  cnf(c_0_208, negated_conjecture, (k4_lattices(esk6_0,esk8_0,k5_lattices(esk6_0))=k5_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_186]), c_0_49]), c_0_151]), c_0_34]), c_0_35]), c_0_137])]), c_0_36])).
% 9.32/9.51  cnf(c_0_209, negated_conjecture, (k3_lattices(esk6_0,k5_lattices(esk6_0),k4_lattices(esk6_0,esk7_0,esk8_0))=k4_lattices(esk6_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192, c_0_196]), c_0_197]), c_0_43]), c_0_137])])).
% 9.32/9.51  cnf(c_0_210, negated_conjecture, (k4_lattices(esk6_0,esk7_0,k3_lattices(esk6_0,esk7_0,esk8_0))=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192, c_0_157]), c_0_198]), c_0_157]), c_0_137]), c_0_43])])).
% 9.32/9.51  cnf(c_0_211, negated_conjecture, (k3_lattices(esk6_0,X1,esk7_0)=k3_lattices(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199, c_0_87]), c_0_35])])).
% 9.32/9.51  cnf(c_0_212, negated_conjecture, (k4_lattices(esk6_0,k6_lattices(esk6_0),k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk7_0))=k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),k4_lattices(esk6_0,esk7_0,esk8_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_102]), c_0_49]), c_0_56])]), c_0_167])).
% 9.32/9.51  cnf(c_0_213, negated_conjecture, (k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk7_0)=k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189, c_0_200]), c_0_49])])).
% 9.32/9.51  cnf(c_0_214, negated_conjecture, (k4_lattices(esk6_0,k6_lattices(esk6_0),k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)))=k3_lattices(esk6_0,esk7_0,k4_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),k7_lattices(esk6_0,esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201, c_0_140]), c_0_116]), c_0_43])])).
% 9.32/9.51  cnf(c_0_215, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 9.32/9.51  cnf(c_0_216, negated_conjecture, (k4_lattices(esk6_0,k5_lattices(esk6_0),k7_lattices(esk6_0,esk8_0))=k5_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_56]), c_0_151]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_217, negated_conjecture, (k4_lattices(esk6_0,esk8_0,k6_lattices(esk6_0))=esk8_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_186]), c_0_49]), c_0_127]), c_0_34]), c_0_35]), c_0_122])]), c_0_36])).
% 9.32/9.51  cnf(c_0_218, negated_conjecture, (k4_lattices(esk6_0,k7_lattices(esk6_0,k4_lattices(esk6_0,X1,esk7_0)),k3_lattices(esk6_0,k7_lattices(esk6_0,X1),esk7_0))=k3_lattices(esk6_0,k7_lattices(esk6_0,X1),k5_lattices(esk6_0))|~m1_subset_1(k7_lattices(esk6_0,X1),u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_114]), c_0_143]), c_0_116])])).
% 9.32/9.51  cnf(c_0_219, negated_conjecture, (k4_lattices(esk6_0,k7_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0)),esk7_0)=esk7_0|k5_lattices(esk6_0)=k4_lattices(esk6_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_202, c_0_87]), c_0_35])])).
% 9.32/9.51  cnf(c_0_220, negated_conjecture, (k3_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0),esk7_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_203, c_0_204])])).
% 9.32/9.51  cnf(c_0_221, negated_conjecture, (k3_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,esk8_0),k5_lattices(esk6_0))=k4_lattices(esk6_0,esk7_0,esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205, c_0_196]), c_0_206]), c_0_207]), c_0_208]), c_0_43]), c_0_137])]), c_0_209]), c_0_210])).
% 9.32/9.51  cnf(c_0_222, negated_conjecture, (k3_lattices(esk6_0,esk7_0,k6_lattices(esk6_0))=k6_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_211]), c_0_43]), c_0_127]), c_0_34]), c_0_35]), c_0_122])]), c_0_36])).
% 9.32/9.51  cnf(c_0_223, negated_conjecture, (k4_lattices(esk6_0,k6_lattices(esk6_0),k7_lattices(esk6_0,esk8_0))=k7_lattices(esk6_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_56]), c_0_127]), c_0_34]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_224, negated_conjecture, (k3_lattices(esk6_0,esk7_0,k4_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),k7_lattices(esk6_0,esk8_0)))=k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),k4_lattices(esk6_0,esk7_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_212, c_0_213]), c_0_214])).
% 9.32/9.51  cnf(c_0_225, negated_conjecture, (k4_lattices(esk6_0,esk7_0,esk8_0)!=k5_lattices(esk6_0)|~r3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.32/9.51  cnf(c_0_226, negated_conjecture, (r3_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))|~r1_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_215, c_0_56]), c_0_44]), c_0_45]), c_0_46]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_227, negated_conjecture, (r1_lattices(esk6_0,k4_lattices(esk6_0,esk7_0,X1),X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_131]), c_0_43]), c_0_45]), c_0_46]), c_0_35])]), c_0_36])).
% 9.32/9.51  cnf(c_0_228, negated_conjecture, (k4_lattices(esk6_0,esk7_0,k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)))=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201, c_0_157]), c_0_216]), c_0_157]), c_0_137]), c_0_43])])).
% 9.32/9.51  cnf(c_0_229, negated_conjecture, (k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),k5_lattices(esk6_0))=k7_lattices(esk6_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_217]), c_0_49])])).
% 9.32/9.51  cnf(c_0_230, negated_conjecture, (k5_lattices(esk6_0)=k4_lattices(esk6_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_218, c_0_219]), c_0_146]), c_0_220]), c_0_143]), c_0_146]), c_0_221]), c_0_146]), c_0_188]), c_0_204])])).
% 9.32/9.51  cnf(c_0_231, negated_conjecture, (k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),k4_lattices(esk6_0,esk7_0,esk8_0))=k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201, c_0_222]), c_0_223]), c_0_122]), c_0_43])]), c_0_214]), c_0_224])).
% 9.32/9.51  cnf(c_0_232, negated_conjecture, (k5_lattices(esk6_0)!=k4_lattices(esk6_0,esk7_0,esk8_0)|~r1_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_225, c_0_226]), c_0_43])])).
% 9.32/9.51  cnf(c_0_233, negated_conjecture, (r1_lattices(esk6_0,esk7_0,k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)))|~m1_subset_1(k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_227, c_0_228])).
% 9.32/9.51  cnf(c_0_234, negated_conjecture, (k3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0))=k7_lattices(esk6_0,esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_229, c_0_230]), c_0_231])).
% 9.32/9.51  cnf(c_0_235, negated_conjecture, (~r1_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_232, c_0_230])])).
% 9.32/9.51  cnf(c_0_236, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_233, c_0_234]), c_0_234]), c_0_56])]), c_0_235]), ['proof']).
% 9.32/9.51  # SZS output end CNFRefutation
% 9.32/9.51  # Proof object total steps             : 237
% 9.32/9.51  # Proof object clause steps            : 178
% 9.32/9.51  # Proof object formula steps           : 59
% 9.32/9.51  # Proof object conjectures             : 143
% 9.32/9.51  # Proof object clause conjectures      : 140
% 9.32/9.51  # Proof object formula conjectures     : 3
% 9.32/9.51  # Proof object initial clauses used    : 44
% 9.32/9.51  # Proof object initial formulas used   : 29
% 9.32/9.51  # Proof object generating inferences   : 127
% 9.32/9.51  # Proof object simplifying inferences  : 546
% 9.32/9.51  # Training examples: 0 positive, 0 negative
% 9.32/9.51  # Parsed axioms                        : 33
% 9.32/9.51  # Removed by relevancy pruning/SinE    : 0
% 9.32/9.51  # Initial clauses                      : 61
% 9.32/9.51  # Removed in clause preprocessing      : 3
% 9.32/9.51  # Initial clauses in saturation        : 58
% 9.32/9.51  # Processed clauses                    : 14066
% 9.32/9.51  # ...of these trivial                  : 717
% 9.32/9.51  # ...subsumed                          : 8784
% 9.32/9.51  # ...remaining for further processing  : 4565
% 9.32/9.51  # Other redundant clauses eliminated   : 0
% 9.32/9.51  # Clauses deleted for lack of memory   : 0
% 9.32/9.51  # Backward-subsumed                    : 718
% 9.32/9.51  # Backward-rewritten                   : 2052
% 9.32/9.51  # Generated clauses                    : 505060
% 9.32/9.51  # ...of the previous two non-trivial   : 464403
% 9.32/9.51  # Contextual simplify-reflections      : 70
% 9.32/9.51  # Paramodulations                      : 505058
% 9.32/9.51  # Factorizations                       : 0
% 9.32/9.51  # Equation resolutions                 : 2
% 9.32/9.51  # Propositional unsat checks           : 0
% 9.32/9.51  #    Propositional check models        : 0
% 9.32/9.51  #    Propositional check unsatisfiable : 0
% 9.32/9.51  #    Propositional clauses             : 0
% 9.32/9.51  #    Propositional clauses after purity: 0
% 9.32/9.51  #    Propositional unsat core size     : 0
% 9.32/9.51  #    Propositional preprocessing time  : 0.000
% 9.32/9.51  #    Propositional encoding time       : 0.000
% 9.32/9.51  #    Propositional solver time         : 0.000
% 9.32/9.51  #    Success case prop preproc time    : 0.000
% 9.32/9.51  #    Success case prop encoding time   : 0.000
% 9.32/9.51  #    Success case prop solver time     : 0.000
% 9.32/9.51  # Current number of processed clauses  : 1795
% 9.32/9.51  #    Positive orientable unit clauses  : 172
% 9.32/9.51  #    Positive unorientable unit clauses: 0
% 9.32/9.51  #    Negative unit clauses             : 9
% 9.32/9.51  #    Non-unit-clauses                  : 1614
% 9.32/9.51  # Current number of unprocessed clauses: 448645
% 9.32/9.51  # ...number of literals in the above   : 2733313
% 9.32/9.51  # Current number of archived formulas  : 0
% 9.32/9.51  # Current number of archived clauses   : 2770
% 9.32/9.51  # Clause-clause subsumption calls (NU) : 1636496
% 9.32/9.51  # Rec. Clause-clause subsumption calls : 675244
% 9.32/9.51  # Non-unit clause-clause subsumptions  : 8942
% 9.32/9.51  # Unit Clause-clause subsumption calls : 36536
% 9.32/9.51  # Rewrite failures with RHS unbound    : 0
% 9.32/9.51  # BW rewrite match attempts            : 11051
% 9.32/9.51  # BW rewrite match successes           : 103
% 9.32/9.51  # Condensation attempts                : 0
% 9.32/9.51  # Condensation successes               : 0
% 9.32/9.51  # Termbank termtop insertions          : 35226337
% 9.32/9.55  
% 9.32/9.55  # -------------------------------------------------
% 9.32/9.55  # User time                : 8.879 s
% 9.32/9.55  # System time              : 0.324 s
% 9.32/9.55  # Total time               : 9.204 s
% 9.32/9.55  # Maximum resident set size: 1620 pages
%------------------------------------------------------------------------------
