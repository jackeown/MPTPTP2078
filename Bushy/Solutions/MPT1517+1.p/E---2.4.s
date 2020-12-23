%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattice3__t51_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:59 EDT 2019

% Result     : Theorem 234.35s
% Output     : CNFRefutation 234.35s
% Verified   : 
% Statistics : Number of formulae       :  103 (1119 expanded)
%              Number of clauses        :   68 ( 411 expanded)
%              Number of leaves         :   17 ( 286 expanded)
%              Depth                    :   23
%              Number of atoms          :  598 (8545 expanded)
%              Number of equality atoms :   61 ( 936 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   28 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',redefinition_k3_lattices)).

fof(commutativity_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',commutativity_k3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',cc1_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',dt_l3_lattices)).

fof(t51_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v14_lattices(X1)
        & l3_lattices(X1)
        & k6_lattices(X1) = k15_lattice3(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',t51_lattice3)).

fof(d17_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ( v14_lattices(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( X2 = k6_lattices(X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( k1_lattices(X1,X2,X3) = X2
                    & k1_lattices(X1,X3,X2) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',d17_lattices)).

fof(d14_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ( v14_lattices(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( k1_lattices(X1,X2,X3) = X2
                  & k1_lattices(X1,X3,X2) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',d14_lattices)).

fof(dt_k6_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => m1_subset_1(k6_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',dt_k6_lattices)).

fof(t22_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_lattices(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => r1_lattices(X1,X2,k1_lattices(X1,X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',t22_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',t26_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',redefinition_r3_lattices)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',fc2_struct_0)).

fof(dt_l2_lattices,axiom,(
    ! [X1] :
      ( l2_lattices(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',dt_l2_lattices)).

fof(t38_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r2_hidden(X2,X3)
             => ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
                & r3_lattices(X1,k16_lattice3(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',t38_lattice3)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',t2_subset)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',dt_k15_lattice3)).

fof(dt_k1_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k1_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',dt_k1_lattices)).

fof(c_0_17,plain,(
    ! [X51,X52,X53] :
      ( v2_struct_0(X51)
      | ~ v4_lattices(X51)
      | ~ l2_lattices(X51)
      | ~ m1_subset_1(X52,u1_struct_0(X51))
      | ~ m1_subset_1(X53,u1_struct_0(X51))
      | k3_lattices(X51,X52,X53) = k1_lattices(X51,X52,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

fof(c_0_18,plain,(
    ! [X8,X9,X10] :
      ( v2_struct_0(X8)
      | ~ v4_lattices(X8)
      | ~ l2_lattices(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | k3_lattices(X8,X9,X10) = k3_lattices(X8,X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,plain,
    ( k3_lattices(X1,X2,X3) = k1_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_22,plain,(
    ! [X93] :
      ( ( ~ v2_struct_0(X93)
        | v2_struct_0(X93)
        | ~ v10_lattices(X93)
        | ~ l3_lattices(X93) )
      & ( v4_lattices(X93)
        | v2_struct_0(X93)
        | ~ v10_lattices(X93)
        | ~ l3_lattices(X93) )
      & ( v5_lattices(X93)
        | v2_struct_0(X93)
        | ~ v10_lattices(X93)
        | ~ l3_lattices(X93) )
      & ( v6_lattices(X93)
        | v2_struct_0(X93)
        | ~ v10_lattices(X93)
        | ~ l3_lattices(X93) )
      & ( v7_lattices(X93)
        | v2_struct_0(X93)
        | ~ v10_lattices(X93)
        | ~ l3_lattices(X93) )
      & ( v8_lattices(X93)
        | v2_struct_0(X93)
        | ~ v10_lattices(X93)
        | ~ l3_lattices(X93) )
      & ( v9_lattices(X93)
        | v2_struct_0(X93)
        | ~ v10_lattices(X93)
        | ~ l3_lattices(X93) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_23,plain,(
    ! [X37] :
      ( ( l1_lattices(X37)
        | ~ l3_lattices(X37) )
      & ( l2_lattices(X37)
        | ~ l3_lattices(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v14_lattices(X1)
          & l3_lattices(X1)
          & k6_lattices(X1) = k15_lattice3(X1,u1_struct_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t51_lattice3])).

cnf(c_0_25,plain,
    ( k1_lattices(X1,X2,X3) = k1_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_21])).

cnf(c_0_26,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v4_lattice3(esk1_0)
    & l3_lattices(esk1_0)
    & ( v2_struct_0(esk1_0)
      | ~ v10_lattices(esk1_0)
      | ~ v14_lattices(esk1_0)
      | ~ l3_lattices(esk1_0)
      | k6_lattices(esk1_0) != k15_lattice3(esk1_0,u1_struct_0(esk1_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).

fof(c_0_29,plain,(
    ! [X16,X17,X18] :
      ( ( k1_lattices(X16,X17,X18) = X17
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | X17 != k6_lattices(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v14_lattices(X16)
        | v2_struct_0(X16)
        | ~ l2_lattices(X16) )
      & ( k1_lattices(X16,X18,X17) = X17
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | X17 != k6_lattices(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v14_lattices(X16)
        | v2_struct_0(X16)
        | ~ l2_lattices(X16) )
      & ( m1_subset_1(esk4_2(X16,X17),u1_struct_0(X16))
        | X17 = k6_lattices(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v14_lattices(X16)
        | v2_struct_0(X16)
        | ~ l2_lattices(X16) )
      & ( k1_lattices(X16,X17,esk4_2(X16,X17)) != X17
        | k1_lattices(X16,esk4_2(X16,X17),X17) != X17
        | X17 = k6_lattices(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ v14_lattices(X16)
        | v2_struct_0(X16)
        | ~ l2_lattices(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattices])])])])])])).

cnf(c_0_30,plain,
    ( k1_lattices(X1,X2,X3) = k1_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( X2 = k6_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,esk4_2(X1,X2)) != X2
    | k1_lattices(X1,esk4_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v14_lattices(X1)
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k1_lattices(esk1_0,X1,X2) = k1_lattices(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])]),c_0_33])).

fof(c_0_36,plain,(
    ! [X11,X13,X14] :
      ( ( m1_subset_1(esk2_1(X11),u1_struct_0(X11))
        | ~ v14_lattices(X11)
        | v2_struct_0(X11)
        | ~ l2_lattices(X11) )
      & ( k1_lattices(X11,esk2_1(X11),X13) = esk2_1(X11)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ v14_lattices(X11)
        | v2_struct_0(X11)
        | ~ l2_lattices(X11) )
      & ( k1_lattices(X11,X13,esk2_1(X11)) = esk2_1(X11)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ v14_lattices(X11)
        | v2_struct_0(X11)
        | ~ l2_lattices(X11) )
      & ( m1_subset_1(esk3_2(X11,X14),u1_struct_0(X11))
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | v14_lattices(X11)
        | v2_struct_0(X11)
        | ~ l2_lattices(X11) )
      & ( k1_lattices(X11,X14,esk3_2(X11,X14)) != X14
        | k1_lattices(X11,esk3_2(X11,X14),X14) != X14
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | v14_lattices(X11)
        | v2_struct_0(X11)
        | ~ l2_lattices(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d14_lattices])])])])])])).

fof(c_0_37,plain,(
    ! [X34] :
      ( v2_struct_0(X34)
      | ~ l2_lattices(X34)
      | m1_subset_1(k6_lattices(X34),u1_struct_0(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_lattices])])])).

cnf(c_0_38,negated_conjecture,
    ( X1 = k6_lattices(esk1_0)
    | k1_lattices(esk1_0,X1,esk4_2(esk1_0,X1)) != X1
    | ~ m1_subset_1(esk4_2(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0)
    | ~ v14_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_33])).

cnf(c_0_39,plain,
    ( k1_lattices(X1,esk2_1(X1),X2) = esk2_1(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v14_lattices(X1)
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_40,plain,(
    ! [X66,X67,X68] :
      ( v2_struct_0(X66)
      | ~ v5_lattices(X66)
      | ~ v6_lattices(X66)
      | ~ v8_lattices(X66)
      | ~ v9_lattices(X66)
      | ~ l3_lattices(X66)
      | ~ m1_subset_1(X67,u1_struct_0(X66))
      | ~ m1_subset_1(X68,u1_struct_0(X66))
      | r1_lattices(X66,X67,k1_lattices(X66,X67,X68)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_lattices])])])])).

cnf(c_0_41,plain,
    ( k1_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | X2 != k6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v14_lattices(X1)
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( esk2_1(esk1_0) = k6_lattices(esk1_0)
    | ~ m1_subset_1(esk4_2(esk1_0,esk2_1(esk1_0)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk2_1(esk1_0),u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0)
    | ~ v14_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_33])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | X2 = k6_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v14_lattices(X1)
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_45,plain,(
    ! [X69,X70,X71] :
      ( v2_struct_0(X69)
      | ~ v4_lattices(X69)
      | ~ l2_lattices(X69)
      | ~ m1_subset_1(X70,u1_struct_0(X69))
      | ~ m1_subset_1(X71,u1_struct_0(X69))
      | ~ r1_lattices(X69,X70,X71)
      | ~ r1_lattices(X69,X71,X70)
      | X70 = X71 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

fof(c_0_46,plain,(
    ! [X58,X59,X60] :
      ( ( ~ r3_lattices(X58,X59,X60)
        | r1_lattices(X58,X59,X60)
        | v2_struct_0(X58)
        | ~ v6_lattices(X58)
        | ~ v8_lattices(X58)
        | ~ v9_lattices(X58)
        | ~ l3_lattices(X58)
        | ~ m1_subset_1(X59,u1_struct_0(X58))
        | ~ m1_subset_1(X60,u1_struct_0(X58)) )
      & ( ~ r1_lattices(X58,X59,X60)
        | r3_lattices(X58,X59,X60)
        | v2_struct_0(X58)
        | ~ v6_lattices(X58)
        | ~ v8_lattices(X58)
        | ~ v9_lattices(X58)
        | ~ l3_lattices(X58)
        | ~ m1_subset_1(X59,u1_struct_0(X58))
        | ~ m1_subset_1(X60,u1_struct_0(X58)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,X2,k1_lattices(X1,X2,X3))
    | ~ v5_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( v5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_49,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_50,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_51,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_52,plain,
    ( k1_lattices(X1,k6_lattices(X1),X2) = k6_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v14_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_41]),c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( esk2_1(esk1_0) = k6_lattices(esk1_0)
    | ~ m1_subset_1(esk2_1(esk1_0),u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0)
    | ~ v14_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_33])).

cnf(c_0_54,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v14_lattices(X1)
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

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
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( r1_lattices(X1,X2,k1_lattices(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k1_lattices(esk1_0,X1,k6_lattices(esk1_0)) = k6_lattices(esk1_0)
    | ~ m1_subset_1(k6_lattices(esk1_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0)
    | ~ v14_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_35]),c_0_33])).

cnf(c_0_59,negated_conjecture,
    ( esk2_1(esk1_0) = k6_lattices(esk1_0)
    | ~ l2_lattices(esk1_0)
    | ~ v14_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_33])).

fof(c_0_60,plain,(
    ! [X94] :
      ( v2_struct_0(X94)
      | ~ l1_struct_0(X94)
      | ~ v1_xboole_0(u1_struct_0(X94)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_61,plain,(
    ! [X36] :
      ( ~ l2_lattices(X36)
      | l1_struct_0(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l2_lattices])])).

cnf(c_0_62,plain,
    ( X1 = X2
    | v2_struct_0(X3)
    | ~ r1_lattices(X3,X1,X2)
    | ~ r3_lattices(X3,X2,X1)
    | ~ v9_lattices(X3)
    | ~ v8_lattices(X3)
    | ~ v6_lattices(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v4_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_27])).

cnf(c_0_63,negated_conjecture,
    ( r1_lattices(esk1_0,X1,k6_lattices(esk1_0))
    | ~ m1_subset_1(k6_lattices(esk1_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0)
    | ~ v14_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_32]),c_0_31])]),c_0_33])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k6_lattices(esk1_0),u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0)
    | ~ v14_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_59]),c_0_33])).

fof(c_0_65,plain,(
    ! [X77,X78,X79] :
      ( ( r3_lattices(X77,X78,k15_lattice3(X77,X79))
        | ~ r2_hidden(X78,X79)
        | ~ m1_subset_1(X78,u1_struct_0(X77))
        | v2_struct_0(X77)
        | ~ v10_lattices(X77)
        | ~ v4_lattice3(X77)
        | ~ l3_lattices(X77) )
      & ( r3_lattices(X77,k16_lattice3(X77,X79),X78)
        | ~ r2_hidden(X78,X79)
        | ~ m1_subset_1(X78,u1_struct_0(X77))
        | v2_struct_0(X77)
        | ~ v10_lattices(X77)
        | ~ v4_lattice3(X77)
        | ~ l3_lattices(X77) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

fof(c_0_66,plain,(
    ! [X72,X73] :
      ( ~ m1_subset_1(X72,X73)
      | v1_xboole_0(X73)
      | r2_hidden(X72,X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( l1_struct_0(X1)
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( X1 = k6_lattices(esk1_0)
    | ~ r3_lattices(esk1_0,k6_lattices(esk1_0),X1)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ v14_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_32])]),c_0_33]),c_0_64])).

cnf(c_0_70,plain,
    ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( v4_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_72,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ l3_lattices(X20)
      | m1_subset_1(k15_lattice3(X20,X21),u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

cnf(c_0_73,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | ~ v10_lattices(esk1_0)
    | ~ v14_lattices(esk1_0)
    | ~ l3_lattices(esk1_0)
    | k6_lattices(esk1_0) != k15_lattice3(esk1_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_76,negated_conjecture,
    ( k15_lattice3(esk1_0,X1) = k6_lattices(esk1_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(k15_lattice3(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ r2_hidden(k6_lattices(esk1_0),X1)
    | ~ v14_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_32]),c_0_71]),c_0_31])]),c_0_33]),c_0_64])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_78,plain,
    ( r2_hidden(esk2_1(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l2_lattices(X1)
    | ~ v14_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_54]),c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( k15_lattice3(esk1_0,u1_struct_0(esk1_0)) != k6_lattices(esk1_0)
    | ~ v14_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_80,negated_conjecture,
    ( k15_lattice3(esk1_0,X1) = k6_lattices(esk1_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ r2_hidden(k6_lattices(esk1_0),X1)
    | ~ v14_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_32])]),c_0_33])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(k6_lattices(esk1_0),u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0)
    | ~ v14_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_59]),c_0_33])).

cnf(c_0_82,plain,
    ( k1_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,k1_lattices(X1,X2,X3),X2)
    | ~ m1_subset_1(k1_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_57]),c_0_26]),c_0_49]),c_0_50]),c_0_51])).

fof(c_0_83,plain,(
    ! [X24,X25,X26] :
      ( v2_struct_0(X24)
      | ~ l2_lattices(X24)
      | ~ m1_subset_1(X25,u1_struct_0(X24))
      | ~ m1_subset_1(X26,u1_struct_0(X24))
      | m1_subset_1(k1_lattices(X24,X25,X26),u1_struct_0(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_lattices])])])).

cnf(c_0_84,negated_conjecture,
    ( ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ v14_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( k1_lattices(esk1_0,X1,X2) = X2
    | ~ r3_lattices(esk1_0,k1_lattices(esk1_0,X1,X2),X2)
    | ~ m1_subset_1(k1_lattices(esk1_0,X1,X2),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_35]),c_0_32]),c_0_31])]),c_0_33])).

cnf(c_0_86,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ v14_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_51]),c_0_32]),c_0_31])]),c_0_33])).

cnf(c_0_88,negated_conjecture,
    ( k1_lattices(esk1_0,X1,k15_lattice3(esk1_0,X2)) = k15_lattice3(esk1_0,X2)
    | ~ m1_subset_1(k1_lattices(esk1_0,X1,k15_lattice3(esk1_0,X2)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k15_lattice3(esk1_0,X2),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(k1_lattices(esk1_0,X1,k15_lattice3(esk1_0,X2)),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_70]),c_0_32]),c_0_71]),c_0_31])]),c_0_33])).

cnf(c_0_89,plain,
    ( r2_hidden(k1_lattices(X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_86]),c_0_74])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(k1_lattices(esk1_0,X1,X2),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_35]),c_0_33])).

cnf(c_0_91,negated_conjecture,
    ( ~ v6_lattices(esk1_0)
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ v14_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_50]),c_0_32]),c_0_31])]),c_0_33])).

cnf(c_0_92,plain,
    ( v14_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | k1_lattices(X1,esk3_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_93,negated_conjecture,
    ( k1_lattices(esk1_0,X1,k15_lattice3(esk1_0,u1_struct_0(esk1_0))) = k15_lattice3(esk1_0,u1_struct_0(esk1_0))
    | ~ m1_subset_1(k15_lattice3(esk1_0,u1_struct_0(esk1_0)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_33]),c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ v14_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_49]),c_0_32]),c_0_31])]),c_0_33])).

cnf(c_0_95,negated_conjecture,
    ( v14_lattices(esk1_0)
    | k1_lattices(esk1_0,X1,esk3_2(esk1_0,X1)) != X1
    | ~ m1_subset_1(esk3_2(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_35]),c_0_33])).

cnf(c_0_96,negated_conjecture,
    ( k1_lattices(esk1_0,k15_lattice3(esk1_0,u1_struct_0(esk1_0)),X1) = k15_lattice3(esk1_0,u1_struct_0(esk1_0))
    | ~ m1_subset_1(k15_lattice3(esk1_0,u1_struct_0(esk1_0)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( ~ l2_lattices(esk1_0)
    | ~ v14_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_26]),c_0_32]),c_0_31])]),c_0_33])).

cnf(c_0_98,negated_conjecture,
    ( ~ m1_subset_1(esk3_2(esk1_0,k15_lattice3(esk1_0,u1_struct_0(esk1_0))),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k15_lattice3(esk1_0,u1_struct_0(esk1_0)),u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97])).

cnf(c_0_99,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v14_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_100,negated_conjecture,
    ( ~ m1_subset_1(k15_lattice3(esk1_0,u1_struct_0(esk1_0)),u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_33]),c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( ~ l2_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_77]),c_0_32])]),c_0_33])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_27]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
