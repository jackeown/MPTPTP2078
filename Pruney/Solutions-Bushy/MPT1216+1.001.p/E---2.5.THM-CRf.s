%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1216+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:55 EST 2020

% Result     : Theorem 20.07s
% Output     : CNFRefutation 20.07s
% Verified   : 
% Statistics : Number of formulae       :  199 (16393 expanded)
%              Number of clauses        :  150 (5400 expanded)
%              Number of leaves         :   24 (4056 expanded)
%              Depth                    :   27
%              Number of atoms          :  818 (105698 expanded)
%              Number of equality atoms :  125 (13089 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_lattices)).

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

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(t47_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattices(X1,k7_lattices(X1,X2),X2) = k5_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattices)).

fof(dt_k7_lattices,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(dt_k2_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattices)).

fof(cc5_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v17_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v11_lattices(X1)
          & v15_lattices(X1)
          & v16_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).

fof(t26_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_lattices(X1,X2,X3)
                  & r1_lattices(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).

fof(cc4_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v15_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v13_lattices(X1)
          & v14_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_lattices)).

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

fof(t41_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r3_lattices(X1,k5_lattices(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattices)).

fof(t27_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v7_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattices(X1,X2,X3)
                   => r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_lattices)).

fof(commutativity_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(t48_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k3_lattices(X1,k7_lattices(X1,X2),X2) = k6_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattices)).

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(dt_k1_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k1_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattices)).

fof(d11_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v11_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => k2_lattices(X1,X2,k1_lattices(X1,X3,X4)) = k1_lattices(X1,k2_lattices(X1,X2,X3),k2_lattices(X1,X2,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_lattices)).

fof(d8_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v8_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

fof(t43_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v14_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattices(X1,k6_lattices(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).

fof(d3_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k1_lattices(X1,X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

fof(t39_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k3_lattices(X1,k5_lattices(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_lattices)).

fof(c_0_24,negated_conjecture,(
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

fof(c_0_25,plain,(
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

fof(c_0_26,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).

fof(c_0_27,plain,(
    ! [X11,X12,X13] :
      ( v2_struct_0(X11)
      | ~ v6_lattices(X11)
      | ~ l1_lattices(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | ~ m1_subset_1(X13,u1_struct_0(X11))
      | k4_lattices(X11,X12,X13) = k4_lattices(X11,X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_28,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( v10_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( l3_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v6_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),c_0_31])).

fof(c_0_35,plain,(
    ! [X40] :
      ( ( l1_lattices(X40)
        | ~ l3_lattices(X40) )
      & ( l2_lattices(X40)
        | ~ l3_lattices(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_36,plain,(
    ! [X63,X64] :
      ( v2_struct_0(X63)
      | ~ v10_lattices(X63)
      | ~ v17_lattices(X63)
      | ~ l3_lattices(X63)
      | ~ m1_subset_1(X64,u1_struct_0(X63))
      | k4_lattices(X63,k7_lattices(X63,X64),X64) = k5_lattices(X63) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattices])])])])).

fof(c_0_37,plain,(
    ! [X38,X39] :
      ( v2_struct_0(X38)
      | ~ l3_lattices(X38)
      | ~ m1_subset_1(X39,u1_struct_0(X38))
      | m1_subset_1(k7_lattices(X38,X39),u1_struct_0(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).

fof(c_0_38,plain,(
    ! [X44,X45,X46] :
      ( v2_struct_0(X44)
      | ~ v6_lattices(X44)
      | ~ l1_lattices(X44)
      | ~ m1_subset_1(X45,u1_struct_0(X44))
      | ~ m1_subset_1(X46,u1_struct_0(X44))
      | k4_lattices(X44,X45,X46) = k2_lattices(X44,X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

cnf(c_0_39,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk7_0) = k4_lattices(esk6_0,esk7_0,X1)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_31]),c_0_34])])).

cnf(c_0_40,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_41,plain,(
    ! [X35,X36,X37] :
      ( v2_struct_0(X35)
      | ~ v6_lattices(X35)
      | ~ l1_lattices(X35)
      | ~ m1_subset_1(X36,u1_struct_0(X35))
      | ~ m1_subset_1(X37,u1_struct_0(X35))
      | m1_subset_1(k4_lattices(X35,X36,X37),u1_struct_0(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,k7_lattices(X1,X2),X2) = k5_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( v17_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X32,X33,X34] :
      ( v2_struct_0(X32)
      | ~ l1_lattices(X32)
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | ~ m1_subset_1(X34,u1_struct_0(X32))
      | m1_subset_1(k2_lattices(X32,X33,X34),u1_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattices])])])).

fof(c_0_47,plain,(
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

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk7_0) = k4_lattices(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_30])])).

fof(c_0_50,plain,(
    ! [X50,X51,X52] :
      ( v2_struct_0(X50)
      | ~ v4_lattices(X50)
      | ~ l2_lattices(X50)
      | ~ m1_subset_1(X51,u1_struct_0(X50))
      | ~ m1_subset_1(X52,u1_struct_0(X50))
      | ~ r1_lattices(X50,X51,X52)
      | ~ r1_lattices(X50,X52,X51)
      | X51 = X52 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( k4_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk8_0) = k5_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk6_0,esk8_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_43]),c_0_30])]),c_0_31])).

cnf(c_0_54,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_56,plain,(
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

cnf(c_0_57,plain,
    ( v15_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_33]),c_0_30])]),c_0_31])).

cnf(c_0_59,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,X1) = k2_lattices(esk6_0,X1,esk7_0)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_33]),c_0_34])]),c_0_31])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk6_0),u1_struct_0(esk6_0))
    | ~ l1_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_43]),c_0_53]),c_0_34])]),c_0_31])).

cnf(c_0_62,negated_conjecture,
    ( v4_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_29]),c_0_30])]),c_0_31])).

fof(c_0_63,plain,(
    ! [X47,X48,X49] :
      ( ( ~ r3_lattices(X47,X48,X49)
        | r1_lattices(X47,X48,X49)
        | v2_struct_0(X47)
        | ~ v6_lattices(X47)
        | ~ v8_lattices(X47)
        | ~ v9_lattices(X47)
        | ~ l3_lattices(X47)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | ~ m1_subset_1(X49,u1_struct_0(X47)) )
      & ( ~ r1_lattices(X47,X48,X49)
        | r3_lattices(X47,X48,X49)
        | v2_struct_0(X47)
        | ~ v6_lattices(X47)
        | ~ v8_lattices(X47)
        | ~ v9_lattices(X47)
        | ~ l3_lattices(X47)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | ~ m1_subset_1(X49,u1_struct_0(X47)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk6_0,X1,esk7_0),u1_struct_0(esk6_0))
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_33]),c_0_31])).

cnf(c_0_65,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_66,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_67,plain,(
    ! [X59,X60] :
      ( v2_struct_0(X59)
      | ~ v10_lattices(X59)
      | ~ v13_lattices(X59)
      | ~ l3_lattices(X59)
      | ~ m1_subset_1(X60,u1_struct_0(X59))
      | r3_lattices(X59,k5_lattices(X59),X60) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_lattices])])])])).

cnf(c_0_68,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_69,negated_conjecture,
    ( v15_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_44]),c_0_30])]),c_0_31])).

cnf(c_0_70,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk7_0)) = k5_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_49]),c_0_33]),c_0_44]),c_0_29]),c_0_30]),c_0_58])]),c_0_31])).

cnf(c_0_71,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,X1) = k2_lattices(esk6_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_40]),c_0_30])])).

cnf(c_0_72,negated_conjecture,
    ( X1 = k5_lattices(esk6_0)
    | ~ r1_lattices(esk6_0,k5_lattices(esk6_0),X1)
    | ~ r1_lattices(esk6_0,X1,k5_lattices(esk6_0))
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])]),c_0_31])).

cnf(c_0_73,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk6_0,X1,esk7_0),u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_40]),c_0_30])])).

cnf(c_0_75,negated_conjecture,
    ( v9_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_76,negated_conjecture,
    ( v8_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,k5_lattices(X1),X2)
    | ~ v10_lattices(X1)
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( v13_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_30])]),c_0_31])).

cnf(c_0_79,negated_conjecture,
    ( k2_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),esk7_0) = k5_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_58])])).

cnf(c_0_80,negated_conjecture,
    ( X1 = k5_lattices(esk6_0)
    | ~ r1_lattices(esk6_0,k5_lattices(esk6_0),X1)
    | ~ r1_lattices(esk6_0,X1,k5_lattices(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_40]),c_0_30])])).

cnf(c_0_81,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_82,negated_conjecture,
    ( r1_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,esk7_0))
    | ~ r3_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_76]),c_0_34]),c_0_30])]),c_0_31])).

cnf(c_0_83,negated_conjecture,
    ( r3_lattices(esk6_0,k5_lattices(esk6_0),k2_lattices(esk6_0,X1,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_74]),c_0_78]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk6_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_79]),c_0_58])])).

fof(c_0_85,plain,(
    ! [X53,X54,X55,X56] :
      ( v2_struct_0(X53)
      | ~ v7_lattices(X53)
      | ~ v8_lattices(X53)
      | ~ v9_lattices(X53)
      | ~ l3_lattices(X53)
      | ~ m1_subset_1(X54,u1_struct_0(X53))
      | ~ m1_subset_1(X55,u1_struct_0(X53))
      | ~ m1_subset_1(X56,u1_struct_0(X53))
      | ~ r1_lattices(X53,X54,X55)
      | r1_lattices(X53,k2_lattices(X53,X54,X56),k2_lattices(X53,X55,X56)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_lattices])])])])).

cnf(c_0_86,plain,
    ( v7_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_87,plain,(
    ! [X8,X9,X10] :
      ( v2_struct_0(X8)
      | ~ v4_lattices(X8)
      | ~ l2_lattices(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | k3_lattices(X8,X9,X10) = k3_lattices(X8,X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).

fof(c_0_88,plain,(
    ! [X65,X66] :
      ( v2_struct_0(X65)
      | ~ v10_lattices(X65)
      | ~ v17_lattices(X65)
      | ~ l3_lattices(X65)
      | ~ m1_subset_1(X66,u1_struct_0(X65))
      | k3_lattices(X65,k7_lattices(X65,X66),X66) = k6_lattices(X65) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattices])])])])).

cnf(c_0_89,negated_conjecture,
    ( X1 = k5_lattices(esk6_0)
    | ~ r1_lattices(esk6_0,k5_lattices(esk6_0),X1)
    | ~ r1_lattices(esk6_0,X1,k5_lattices(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_30])])).

cnf(c_0_90,negated_conjecture,
    ( r1_lattices(esk6_0,k5_lattices(esk6_0),k2_lattices(esk6_0,X1,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])])).

cnf(c_0_91,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4))
    | ~ v7_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( v7_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_93,negated_conjecture,
    ( r1_lattices(esk6_0,X1,k7_lattices(esk6_0,esk7_0))
    | ~ r3_lattices(esk6_0,X1,k7_lattices(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_58]),c_0_75]),c_0_76]),c_0_34]),c_0_30])]),c_0_31])).

cnf(c_0_94,negated_conjecture,
    ( r3_lattices(esk6_0,k5_lattices(esk6_0),k7_lattices(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_58]),c_0_78]),c_0_29]),c_0_30])]),c_0_31])).

fof(c_0_95,plain,(
    ! [X41,X42,X43] :
      ( v2_struct_0(X41)
      | ~ v4_lattices(X41)
      | ~ l2_lattices(X41)
      | ~ m1_subset_1(X42,u1_struct_0(X41))
      | ~ m1_subset_1(X43,u1_struct_0(X41))
      | k3_lattices(X41,X42,X43) = k1_lattices(X41,X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

cnf(c_0_96,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_97,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,k7_lattices(X1,X2),X2) = k6_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_98,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk7_0) = k2_lattices(esk6_0,esk7_0,X1)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_33]),c_0_34])]),c_0_31])).

cnf(c_0_99,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk7_0) = k2_lattices(esk6_0,X1,esk7_0)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_33]),c_0_31]),c_0_34])])).

cnf(c_0_100,negated_conjecture,
    ( k2_lattices(esk6_0,X1,esk7_0) = k5_lattices(esk6_0)
    | ~ r1_lattices(esk6_0,k2_lattices(esk6_0,X1,esk7_0),k5_lattices(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_74])).

cnf(c_0_101,negated_conjecture,
    ( r1_lattices(esk6_0,k2_lattices(esk6_0,X1,esk7_0),k5_lattices(esk6_0))
    | ~ r1_lattices(esk6_0,X1,k7_lattices(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_79]),c_0_33]),c_0_58]),c_0_75]),c_0_76]),c_0_92]),c_0_30])]),c_0_31])).

cnf(c_0_102,negated_conjecture,
    ( r1_lattices(esk6_0,k5_lattices(esk6_0),k7_lattices(esk6_0,esk7_0))
    | ~ m1_subset_1(k5_lattices(esk6_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_103,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_104,negated_conjecture,
    ( k3_lattices(esk6_0,X1,esk7_0) = k3_lattices(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_33]),c_0_31]),c_0_62])])).

fof(c_0_105,plain,(
    ! [X29,X30,X31] :
      ( v2_struct_0(X29)
      | ~ l2_lattices(X29)
      | ~ m1_subset_1(X30,u1_struct_0(X29))
      | ~ m1_subset_1(X31,u1_struct_0(X29))
      | m1_subset_1(k1_lattices(X29,X30,X31),u1_struct_0(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_lattices])])])).

cnf(c_0_106,negated_conjecture,
    ( k3_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk8_0) = k6_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_43]),c_0_44]),c_0_29]),c_0_30])]),c_0_31])).

fof(c_0_107,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ v11_lattices(X14)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | k2_lattices(X14,X15,k1_lattices(X14,X16,X17)) = k1_lattices(X14,k2_lattices(X14,X15,X16),k2_lattices(X14,X15,X17))
        | v2_struct_0(X14)
        | ~ l3_lattices(X14) )
      & ( m1_subset_1(esk1_1(X14),u1_struct_0(X14))
        | v11_lattices(X14)
        | v2_struct_0(X14)
        | ~ l3_lattices(X14) )
      & ( m1_subset_1(esk2_1(X14),u1_struct_0(X14))
        | v11_lattices(X14)
        | v2_struct_0(X14)
        | ~ l3_lattices(X14) )
      & ( m1_subset_1(esk3_1(X14),u1_struct_0(X14))
        | v11_lattices(X14)
        | v2_struct_0(X14)
        | ~ l3_lattices(X14) )
      & ( k2_lattices(X14,esk1_1(X14),k1_lattices(X14,esk2_1(X14),esk3_1(X14))) != k1_lattices(X14,k2_lattices(X14,esk1_1(X14),esk2_1(X14)),k2_lattices(X14,esk1_1(X14),esk3_1(X14)))
        | v11_lattices(X14)
        | v2_struct_0(X14)
        | ~ l3_lattices(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_lattices])])])])])])).

cnf(c_0_108,plain,
    ( v11_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_109,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk7_0) = k2_lattices(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_40]),c_0_30])])).

cnf(c_0_110,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk7_0) = k2_lattices(esk6_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_40]),c_0_30])])).

cnf(c_0_111,negated_conjecture,
    ( k2_lattices(esk6_0,X1,esk7_0) = k5_lattices(esk6_0)
    | ~ r1_lattices(esk6_0,X1,k7_lattices(esk6_0,esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_112,negated_conjecture,
    ( r1_lattices(esk6_0,k5_lattices(esk6_0),k7_lattices(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_84])])).

fof(c_0_113,plain,(
    ! [X24,X25,X26] :
      ( ( ~ v8_lattices(X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | k1_lattices(X24,k2_lattices(X24,X25,X26),X26) = X26
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( m1_subset_1(esk4_1(X24),u1_struct_0(X24))
        | v8_lattices(X24)
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( m1_subset_1(esk5_1(X24),u1_struct_0(X24))
        | v8_lattices(X24)
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( k1_lattices(X24,k2_lattices(X24,esk4_1(X24),esk5_1(X24)),esk5_1(X24)) != esk5_1(X24)
        | v8_lattices(X24)
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).

cnf(c_0_114,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk8_0) = k4_lattices(esk6_0,esk8_0,X1)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_43]),c_0_31]),c_0_34])])).

cnf(c_0_115,negated_conjecture,
    ( k3_lattices(esk6_0,X1,esk7_0) = k1_lattices(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_33]),c_0_62])]),c_0_31])).

fof(c_0_116,plain,(
    ! [X61,X62] :
      ( v2_struct_0(X61)
      | ~ v10_lattices(X61)
      | ~ v14_lattices(X61)
      | ~ l3_lattices(X61)
      | ~ m1_subset_1(X62,u1_struct_0(X61))
      | k4_lattices(X61,k6_lattices(X61),X62) = X62 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_lattices])])])])).

cnf(c_0_117,plain,
    ( v14_lattices(X1)
    | v2_struct_0(X1)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_118,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_119,negated_conjecture,
    ( k1_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk8_0) = k6_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_106]),c_0_43]),c_0_53]),c_0_62])]),c_0_31])).

cnf(c_0_120,plain,
    ( k2_lattices(X1,X2,k1_lattices(X1,X3,X4)) = k1_lattices(X1,k2_lattices(X1,X2,X3),k2_lattices(X1,X2,X4))
    | v2_struct_0(X1)
    | ~ v11_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_121,negated_conjecture,
    ( v11_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_44]),c_0_30])]),c_0_31])).

cnf(c_0_122,negated_conjecture,
    ( k2_lattices(esk6_0,X1,esk7_0) = k2_lattices(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_123,negated_conjecture,
    ( k2_lattices(esk6_0,k5_lattices(esk6_0),esk7_0) = k5_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_84])])).

cnf(c_0_124,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_113])).

cnf(c_0_125,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk8_0) = k4_lattices(esk6_0,esk8_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_40]),c_0_30])])).

fof(c_0_126,plain,(
    ! [X21,X22,X23] :
      ( ( ~ r1_lattices(X21,X22,X23)
        | k1_lattices(X21,X22,X23) = X23
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l2_lattices(X21) )
      & ( k1_lattices(X21,X22,X23) != X23
        | r1_lattices(X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l2_lattices(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

cnf(c_0_127,negated_conjecture,
    ( k1_lattices(esk6_0,esk7_0,X1) = k1_lattices(esk6_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_115]),c_0_33]),c_0_62])]),c_0_31])).

cnf(c_0_128,negated_conjecture,
    ( r1_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))
    | ~ r3_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_53]),c_0_75]),c_0_76]),c_0_34]),c_0_30])]),c_0_31])).

cnf(c_0_129,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,esk8_0) = k5_lattices(esk6_0)
    | r3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_130,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk8_0) = k2_lattices(esk6_0,X1,esk8_0)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_43]),c_0_31]),c_0_34])])).

cnf(c_0_131,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,k6_lattices(X1),X2) = X2
    | ~ v10_lattices(X1)
    | ~ v14_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_132,negated_conjecture,
    ( v14_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_69]),c_0_30])]),c_0_31])).

cnf(c_0_133,negated_conjecture,
    ( m1_subset_1(k6_lattices(esk6_0),u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_43]),c_0_53])]),c_0_31])).

cnf(c_0_134,negated_conjecture,
    ( k1_lattices(esk6_0,k2_lattices(esk6_0,X1,X2),k2_lattices(esk6_0,X1,esk7_0)) = k2_lattices(esk6_0,X1,k1_lattices(esk6_0,X2,esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_33]),c_0_30])]),c_0_31]),c_0_121])])).

cnf(c_0_135,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk7_0)) = k5_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_109]),c_0_33]),c_0_44]),c_0_29]),c_0_30]),c_0_58])]),c_0_31])).

cnf(c_0_136,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k5_lattices(esk6_0)) = k5_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_84])])).

cnf(c_0_137,negated_conjecture,
    ( k1_lattices(esk6_0,k5_lattices(esk6_0),esk7_0) = esk7_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_79]),c_0_33]),c_0_58]),c_0_76]),c_0_30])]),c_0_31])).

cnf(c_0_138,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk8_0) = k2_lattices(esk6_0,esk8_0,X1)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_125]),c_0_43]),c_0_34])]),c_0_31])).

cnf(c_0_139,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_126])).

cnf(c_0_140,negated_conjecture,
    ( k1_lattices(esk6_0,esk7_0,X1) = k1_lattices(esk6_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_81]),c_0_30])])).

cnf(c_0_141,negated_conjecture,
    ( k5_lattices(esk6_0) = k4_lattices(esk6_0,esk7_0,esk8_0)
    | r1_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_33])])).

cnf(c_0_142,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,esk8_0) = k2_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_109]),c_0_33]),c_0_43])])).

cnf(c_0_143,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk8_0) = k2_lattices(esk6_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_40]),c_0_30])])).

cnf(c_0_144,negated_conjecture,
    ( k4_lattices(esk6_0,k6_lattices(esk6_0),esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_33]),c_0_29]),c_0_30])]),c_0_31]),c_0_132])])).

cnf(c_0_145,negated_conjecture,
    ( k4_lattices(esk6_0,X1,k6_lattices(esk6_0)) = k4_lattices(esk6_0,k6_lattices(esk6_0),X1)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_133]),c_0_34])]),c_0_31])).

cnf(c_0_146,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k1_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),esk7_0)) = k1_lattices(esk6_0,k5_lattices(esk6_0),k2_lattices(esk6_0,esk7_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_58]),c_0_33])])).

cnf(c_0_147,negated_conjecture,
    ( k1_lattices(esk6_0,k5_lattices(esk6_0),k2_lattices(esk6_0,esk7_0,esk7_0)) = k2_lattices(esk6_0,esk7_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_136]),c_0_137]),c_0_84]),c_0_33])])).

cnf(c_0_148,negated_conjecture,
    ( k3_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),esk7_0) = k6_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_33]),c_0_44]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_149,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk8_0) = k2_lattices(esk6_0,esk8_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_40]),c_0_30])])).

cnf(c_0_150,negated_conjecture,
    ( k1_lattices(esk6_0,X1,esk7_0) = X1
    | ~ r1_lattices(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_33])]),c_0_31])).

cnf(c_0_151,negated_conjecture,
    ( k5_lattices(esk6_0) = k2_lattices(esk6_0,esk7_0,esk8_0)
    | r1_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) ),
    inference(rw,[status(thm)],[c_0_141,c_0_142])).

cnf(c_0_152,negated_conjecture,
    ( k2_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk8_0) = k5_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_143]),c_0_43]),c_0_44]),c_0_29]),c_0_30]),c_0_53])]),c_0_31])).

cnf(c_0_153,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,k6_lattices(esk6_0)) = esk7_0
    | ~ l1_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_145]),c_0_33])])).

cnf(c_0_154,negated_conjecture,
    ( k4_lattices(esk6_0,X1,k6_lattices(esk6_0)) = k2_lattices(esk6_0,X1,k6_lattices(esk6_0))
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_133]),c_0_34])]),c_0_31])).

cnf(c_0_155,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k1_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),esk7_0)) = k2_lattices(esk6_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_156,negated_conjecture,
    ( k1_lattices(esk6_0,k7_lattices(esk6_0,esk7_0),esk7_0) = k6_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_148]),c_0_33]),c_0_58]),c_0_62])]),c_0_31])).

cnf(c_0_157,negated_conjecture,
    ( k2_lattices(esk6_0,esk8_0,k7_lattices(esk6_0,esk8_0)) = k5_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_149]),c_0_43]),c_0_44]),c_0_29]),c_0_30]),c_0_53])]),c_0_31])).

cnf(c_0_158,negated_conjecture,
    ( k1_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk7_0) = k7_lattices(esk6_0,esk8_0)
    | k5_lattices(esk6_0) = k2_lattices(esk6_0,esk7_0,esk8_0)
    | ~ l2_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_151]),c_0_53])])).

cnf(c_0_159,negated_conjecture,
    ( k1_lattices(esk6_0,k2_lattices(esk6_0,X1,X2),k2_lattices(esk6_0,X1,esk8_0)) = k2_lattices(esk6_0,X1,k1_lattices(esk6_0,X2,esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_43]),c_0_30])]),c_0_31]),c_0_121])])).

cnf(c_0_160,negated_conjecture,
    ( k1_lattices(esk6_0,k5_lattices(esk6_0),esk8_0) = esk8_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_152]),c_0_43]),c_0_53]),c_0_76]),c_0_30])]),c_0_31])).

cnf(c_0_161,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k6_lattices(esk6_0)) = esk7_0
    | ~ l1_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_154]),c_0_33])])).

cnf(c_0_162,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k6_lattices(esk6_0)) = k2_lattices(esk6_0,esk7_0,esk7_0)
    | ~ l2_lattices(esk6_0) ),
    inference(spm,[status(thm)],[c_0_155,c_0_156])).

fof(c_0_163,plain,(
    ! [X57,X58] :
      ( v2_struct_0(X57)
      | ~ v10_lattices(X57)
      | ~ v13_lattices(X57)
      | ~ l3_lattices(X57)
      | ~ m1_subset_1(X58,u1_struct_0(X57))
      | k3_lattices(X57,k5_lattices(X57),X58) = X58 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_lattices])])])])).

cnf(c_0_164,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0)),u1_struct_0(esk6_0))
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_53]),c_0_31])).

cnf(c_0_165,negated_conjecture,
    ( k2_lattices(esk6_0,esk8_0,k1_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),X1)) = k1_lattices(esk6_0,k5_lattices(esk6_0),k2_lattices(esk6_0,esk8_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_157]),c_0_53]),c_0_43]),c_0_121]),c_0_30])]),c_0_31])).

cnf(c_0_166,negated_conjecture,
    ( k1_lattices(esk6_0,k7_lattices(esk6_0,esk8_0),esk7_0) = k7_lattices(esk6_0,esk8_0)
    | k5_lattices(esk6_0) = k2_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_81]),c_0_30])])).

cnf(c_0_167,negated_conjecture,
    ( k2_lattices(esk6_0,esk8_0,esk7_0) = k2_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_71]),c_0_43])])).

cnf(c_0_168,negated_conjecture,
    ( k1_lattices(esk6_0,k5_lattices(esk6_0),k2_lattices(esk6_0,esk7_0,esk8_0)) = k2_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_136]),c_0_160]),c_0_84]),c_0_33])])).

cnf(c_0_169,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,esk7_0) = esk7_0
    | ~ l1_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(spm,[status(thm)],[c_0_161,c_0_162])).

cnf(c_0_170,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,k5_lattices(X1),X2) = X2
    | ~ v10_lattices(X1)
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_163])).

cnf(c_0_171,negated_conjecture,
    ( k3_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,k7_lattices(esk6_0,esk8_0))) = k1_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,k7_lattices(esk6_0,esk8_0)))
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_164]),c_0_62])]),c_0_31])).

cnf(c_0_172,negated_conjecture,
    ( k5_lattices(esk6_0) = k2_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_166]),c_0_157]),c_0_167]),c_0_168]),c_0_33])])).

cnf(c_0_173,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_174,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,esk7_0) = esk7_0
    | ~ l2_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_40]),c_0_30])])).

cnf(c_0_175,negated_conjecture,
    ( k1_lattices(esk6_0,k2_lattices(esk6_0,esk7_0,esk8_0),k2_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))) = k2_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_171]),c_0_78]),c_0_29]),c_0_30]),c_0_84])]),c_0_31]),c_0_172]),c_0_164])).

cnf(c_0_176,negated_conjecture,
    ( k3_lattices(esk6_0,esk8_0,k7_lattices(esk6_0,esk8_0)) = k6_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_106]),c_0_43]),c_0_53]),c_0_62])]),c_0_31])).

cnf(c_0_177,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,esk8_0) != k5_lattices(esk6_0)
    | ~ r3_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_178,negated_conjecture,
    ( r3_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))
    | ~ r1_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_53]),c_0_75]),c_0_76]),c_0_34]),c_0_30])]),c_0_31])).

cnf(c_0_179,negated_conjecture,
    ( k4_lattices(esk6_0,k6_lattices(esk6_0),k7_lattices(esk6_0,esk8_0)) = k7_lattices(esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_53]),c_0_132]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_180,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_81]),c_0_30])])).

cnf(c_0_181,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k1_lattices(esk6_0,esk8_0,k7_lattices(esk6_0,esk8_0))) = k2_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0))
    | ~ l1_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_175]),c_0_53]),c_0_43]),c_0_33]),c_0_121]),c_0_30])]),c_0_31])).

cnf(c_0_182,negated_conjecture,
    ( k1_lattices(esk6_0,esk8_0,k7_lattices(esk6_0,esk8_0)) = k6_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_176]),c_0_53]),c_0_43]),c_0_62])]),c_0_31])).

cnf(c_0_183,negated_conjecture,
    ( k5_lattices(esk6_0) != k4_lattices(esk6_0,esk7_0,esk8_0)
    | ~ r1_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_178]),c_0_33])])).

cnf(c_0_184,negated_conjecture,
    ( k2_lattices(esk6_0,k6_lattices(esk6_0),k7_lattices(esk6_0,esk8_0)) = k7_lattices(esk6_0,esk8_0)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(k6_lattices(esk6_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_179]),c_0_53]),c_0_34])]),c_0_31])).

cnf(c_0_185,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k6_lattices(esk6_0)) = esk7_0
    | ~ l2_lattices(esk6_0) ),
    inference(rw,[status(thm)],[c_0_162,c_0_180])).

cnf(c_0_186,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k6_lattices(esk6_0)) = k2_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0))
    | ~ l1_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(spm,[status(thm)],[c_0_181,c_0_182])).

cnf(c_0_187,negated_conjecture,
    ( k5_lattices(esk6_0) != k2_lattices(esk6_0,esk7_0,esk8_0)
    | ~ r1_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) ),
    inference(rw,[status(thm)],[c_0_183,c_0_142])).

cnf(c_0_188,negated_conjecture,
    ( r1_lattices(esk6_0,k2_lattices(esk6_0,X1,k7_lattices(esk6_0,esk8_0)),k7_lattices(esk6_0,esk8_0))
    | ~ r1_lattices(esk6_0,X1,k6_lattices(esk6_0))
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(k6_lattices(esk6_0),u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_184]),c_0_53]),c_0_75]),c_0_76]),c_0_92]),c_0_30])]),c_0_31])).

cnf(c_0_189,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) = esk7_0
    | ~ l1_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(spm,[status(thm)],[c_0_185,c_0_186])).

cnf(c_0_190,negated_conjecture,
    ( ~ r1_lattices(esk6_0,esk7_0,k7_lattices(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_187,c_0_172])])).

cnf(c_0_191,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_126])).

cnf(c_0_192,negated_conjecture,
    ( k1_lattices(esk6_0,k2_lattices(esk6_0,X1,k6_lattices(esk6_0)),k6_lattices(esk6_0)) = k6_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_133]),c_0_76]),c_0_30])]),c_0_31])).

cnf(c_0_193,negated_conjecture,
    ( ~ r1_lattices(esk6_0,esk7_0,k6_lattices(esk6_0))
    | ~ l1_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188,c_0_189]),c_0_33])]),c_0_190]),c_0_133])).

cnf(c_0_194,negated_conjecture,
    ( r1_lattices(esk6_0,X1,k6_lattices(esk6_0))
    | k1_lattices(esk6_0,X1,k6_lattices(esk6_0)) != k6_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_133]),c_0_31])).

cnf(c_0_195,negated_conjecture,
    ( k1_lattices(esk6_0,esk7_0,k6_lattices(esk6_0)) = k6_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_185]),c_0_33])])).

cnf(c_0_196,negated_conjecture,
    ( ~ l1_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193,c_0_194]),c_0_33])]),c_0_195])).

cnf(c_0_197,negated_conjecture,
    ( ~ l2_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196,c_0_40]),c_0_30])])).

cnf(c_0_198,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197,c_0_81]),c_0_30])]),
    [proof]).

%------------------------------------------------------------------------------
