%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattices__t53_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:03 EDT 2019

% Result     : Theorem 163.62s
% Output     : CNFRefutation 163.62s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 551 expanded)
%              Number of clauses        :   72 ( 186 expanded)
%              Number of leaves         :   17 ( 137 expanded)
%              Depth                    :   20
%              Number of atoms          :  596 (3454 expanded)
%              Number of equality atoms :   34 (  55 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   28 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r3_lattices(X1,X2,X3)
               => r3_lattices(X1,k7_lattices(X1,X3),k7_lattices(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',t53_lattices)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',redefinition_k4_lattices)).

fof(t47_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattices(X1,k7_lattices(X1,X2),X2) = k5_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',t47_lattices)).

fof(dt_k7_lattices,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',dt_k7_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',redefinition_r3_lattices)).

fof(dt_k2_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',dt_k2_lattices)).

fof(t41_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r3_lattices(X1,k5_lattices(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',t41_lattices)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',dt_k4_lattices)).

fof(t52_lattices,axiom,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',t52_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',cc1_lattices)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',commutativity_k4_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',t26_lattices)).

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',dt_k5_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',t27_lattices)).

fof(cc4_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v15_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v13_lattices(X1)
          & v14_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',cc4_lattices)).

fof(cc5_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v17_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v11_lattices(X1)
          & v15_lattices(X1)
          & v16_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',cc5_lattices)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v17_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r3_lattices(X1,X2,X3)
                 => r3_lattices(X1,k7_lattices(X1,X3),k7_lattices(X1,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t53_lattices])).

fof(c_0_18,plain,(
    ! [X43,X44,X45] :
      ( v2_struct_0(X43)
      | ~ v6_lattices(X43)
      | ~ l1_lattices(X43)
      | ~ m1_subset_1(X44,u1_struct_0(X43))
      | ~ m1_subset_1(X45,u1_struct_0(X43))
      | k4_lattices(X43,X44,X45) = k2_lattices(X43,X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v17_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & r3_lattices(esk1_0,esk2_0,esk3_0)
    & ~ r3_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_20,plain,(
    ! [X67,X68] :
      ( v2_struct_0(X67)
      | ~ v10_lattices(X67)
      | ~ v17_lattices(X67)
      | ~ l3_lattices(X67)
      | ~ m1_subset_1(X68,u1_struct_0(X67))
      | k4_lattices(X67,k7_lattices(X67,X68),X68) = k5_lattices(X67) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattices])])])])).

fof(c_0_21,plain,(
    ! [X27,X28] :
      ( v2_struct_0(X27)
      | ~ l3_lattices(X27)
      | ~ m1_subset_1(X28,u1_struct_0(X27))
      | m1_subset_1(k7_lattices(X27,X28),u1_struct_0(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).

fof(c_0_22,plain,(
    ! [X31] :
      ( ( l1_lattices(X31)
        | ~ l3_lattices(X31) )
      & ( l2_lattices(X31)
        | ~ l3_lattices(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_23,plain,(
    ! [X46,X47,X48] :
      ( ( ~ r3_lattices(X46,X47,X48)
        | r1_lattices(X46,X47,X48)
        | v2_struct_0(X46)
        | ~ v6_lattices(X46)
        | ~ v8_lattices(X46)
        | ~ v9_lattices(X46)
        | ~ l3_lattices(X46)
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | ~ m1_subset_1(X48,u1_struct_0(X46)) )
      & ( ~ r1_lattices(X46,X47,X48)
        | r3_lattices(X46,X47,X48)
        | v2_struct_0(X46)
        | ~ v6_lattices(X46)
        | ~ v8_lattices(X46)
        | ~ v9_lattices(X46)
        | ~ l3_lattices(X46)
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | ~ m1_subset_1(X48,u1_struct_0(X46)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

fof(c_0_24,plain,(
    ! [X16,X17,X18] :
      ( v2_struct_0(X16)
      | ~ l1_lattices(X16)
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | m1_subset_1(k2_lattices(X16,X17,X18),u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattices])])])).

fof(c_0_25,plain,(
    ! [X65,X66] :
      ( v2_struct_0(X65)
      | ~ v10_lattices(X65)
      | ~ v13_lattices(X65)
      | ~ l3_lattices(X65)
      | ~ m1_subset_1(X66,u1_struct_0(X65))
      | r3_lattices(X65,k5_lattices(X65),X66) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_lattices])])])])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X23,X24,X25] :
      ( v2_struct_0(X23)
      | ~ v6_lattices(X23)
      | ~ l1_lattices(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | m1_subset_1(k4_lattices(X23,X24,X25),u1_struct_0(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,k7_lattices(X1,X2),X2) = k5_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_35,plain,(
    ! [X72,X73,X74] :
      ( ( k4_lattices(X72,X73,X74) != k5_lattices(X72)
        | r3_lattices(X72,X73,k7_lattices(X72,X74))
        | ~ m1_subset_1(X74,u1_struct_0(X72))
        | ~ m1_subset_1(X73,u1_struct_0(X72))
        | v2_struct_0(X72)
        | ~ v10_lattices(X72)
        | ~ v17_lattices(X72)
        | ~ l3_lattices(X72) )
      & ( ~ r3_lattices(X72,X73,k7_lattices(X72,X74))
        | k4_lattices(X72,X73,X74) = k5_lattices(X72)
        | ~ m1_subset_1(X74,u1_struct_0(X72))
        | ~ m1_subset_1(X73,u1_struct_0(X72))
        | v2_struct_0(X72)
        | ~ v10_lattices(X72)
        | ~ v17_lattices(X72)
        | ~ l3_lattices(X72) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_lattices])])])])])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,k5_lattices(X1),X2)
    | ~ v10_lattices(X1)
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_41,plain,(
    ! [X83] :
      ( ( ~ v2_struct_0(X83)
        | v2_struct_0(X83)
        | ~ v10_lattices(X83)
        | ~ l3_lattices(X83) )
      & ( v4_lattices(X83)
        | v2_struct_0(X83)
        | ~ v10_lattices(X83)
        | ~ l3_lattices(X83) )
      & ( v5_lattices(X83)
        | v2_struct_0(X83)
        | ~ v10_lattices(X83)
        | ~ l3_lattices(X83) )
      & ( v6_lattices(X83)
        | v2_struct_0(X83)
        | ~ v10_lattices(X83)
        | ~ l3_lattices(X83) )
      & ( v7_lattices(X83)
        | v2_struct_0(X83)
        | ~ v10_lattices(X83)
        | ~ l3_lattices(X83) )
      & ( v8_lattices(X83)
        | v2_struct_0(X83)
        | ~ v10_lattices(X83)
        | ~ l3_lattices(X83) )
      & ( v9_lattices(X83)
        | v2_struct_0(X83)
        | ~ v10_lattices(X83)
        | ~ l3_lattices(X83) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_42,negated_conjecture,
    ( k2_lattices(esk1_0,X1,esk2_0) = k4_lattices(esk1_0,X1,esk2_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk3_0) = k5_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_28])).

cnf(c_0_45,plain,
    ( r3_lattices(X1,X2,k7_lattices(X1,X3))
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_46,plain,(
    ! [X10,X11,X12] :
      ( v2_struct_0(X10)
      | ~ v6_lattices(X10)
      | ~ l1_lattices(X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | k4_lattices(X10,X11,X12) = k4_lattices(X10,X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_47,plain,
    ( k2_lattices(X1,X2,k7_lattices(X1,X3)) = k4_lattices(X1,X2,k7_lattices(X1,X3))
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_36]),c_0_37])).

fof(c_0_48,plain,(
    ! [X54,X55,X56] :
      ( v2_struct_0(X54)
      | ~ v4_lattices(X54)
      | ~ l2_lattices(X54)
      | ~ m1_subset_1(X55,u1_struct_0(X54))
      | ~ m1_subset_1(X56,u1_struct_0(X54))
      | ~ r1_lattices(X54,X55,X56)
      | ~ r1_lattices(X54,X56,X55)
      | X55 = X56 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

fof(c_0_49,plain,(
    ! [X26] :
      ( v2_struct_0(X26)
      | ~ l1_lattices(X26)
      | m1_subset_1(k5_lattices(X26),u1_struct_0(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

cnf(c_0_50,plain,
    ( r1_lattices(X1,X2,k2_lattices(X1,X3,X4))
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ r3_lattices(X1,X2,k2_lattices(X1,X3,X4))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_37])).

cnf(c_0_51,plain,
    ( r3_lattices(X1,k5_lattices(X1),k2_lattices(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ v13_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_39]),c_0_37])).

cnf(c_0_52,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( k2_lattices(esk1_0,k7_lattices(esk1_0,X1),esk2_0) = k4_lattices(esk1_0,k7_lattices(esk1_0,X1),esk2_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_36]),c_0_32])]),c_0_28])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk1_0),u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_31])]),c_0_28])).

cnf(c_0_57,negated_conjecture,
    ( r3_lattices(esk1_0,X1,k7_lattices(esk1_0,esk2_0))
    | k4_lattices(esk1_0,X1,esk2_0) != k5_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_27]),c_0_32]),c_0_33]),c_0_34])]),c_0_28])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_59,plain,(
    ! [X57,X58,X59,X60] :
      ( v2_struct_0(X57)
      | ~ v7_lattices(X57)
      | ~ v8_lattices(X57)
      | ~ v9_lattices(X57)
      | ~ l3_lattices(X57)
      | ~ m1_subset_1(X58,u1_struct_0(X57))
      | ~ m1_subset_1(X59,u1_struct_0(X57))
      | ~ m1_subset_1(X60,u1_struct_0(X57))
      | ~ r1_lattices(X57,X58,X59)
      | r1_lattices(X57,k2_lattices(X57,X58,X60),k2_lattices(X57,X59,X60)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_lattices])])])])).

cnf(c_0_60,negated_conjecture,
    ( k2_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,X1)) = k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,X1))
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_31]),c_0_32])]),c_0_28])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_62,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_63,plain,
    ( r1_lattices(X1,k5_lattices(X1),k2_lattices(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ v13_lattices(X1)
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( k2_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0) = k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_31])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk1_0),u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_36]),c_0_31]),c_0_32])]),c_0_28])).

cnf(c_0_66,negated_conjecture,
    ( r3_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,esk2_0))
    | k4_lattices(esk1_0,k7_lattices(esk1_0,X1),esk2_0) != k5_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_36]),c_0_32])]),c_0_28])).

cnf(c_0_67,negated_conjecture,
    ( ~ r3_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_68,plain,
    ( k4_lattices(X1,X2,k7_lattices(X1,X3)) = k4_lattices(X1,k7_lattices(X1,X3),X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_36]),c_0_37])).

cnf(c_0_69,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( k2_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk3_0)) = k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk3_0))
    | ~ v6_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_31])).

cnf(c_0_71,negated_conjecture,
    ( k2_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,X1)) = k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,X1))
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_27]),c_0_32])]),c_0_28])).

cnf(c_0_72,negated_conjecture,
    ( r1_lattices(esk1_0,X1,esk3_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ r3_lattices(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_31]),c_0_32])]),c_0_28])).

cnf(c_0_73,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_74,plain,
    ( X1 = k5_lattices(X2)
    | v2_struct_0(X2)
    | ~ v4_lattices(X2)
    | ~ r1_lattices(X2,k5_lattices(X2),X1)
    | ~ r1_lattices(X2,X1,k5_lattices(X2))
    | ~ l2_lattices(X2)
    | ~ l1_lattices(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( r1_lattices(esk1_0,k5_lattices(esk1_0),k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0))
    | ~ v13_lattices(esk1_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_27]),c_0_32]),c_0_34])]),c_0_28]),c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0) != k5_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_31]),c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0),u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_64]),c_0_27])]),c_0_28])).

cnf(c_0_78,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,X1),esk2_0) = k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,X1))
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_27]),c_0_32])]),c_0_28])).

cnf(c_0_79,negated_conjecture,
    ( r1_lattices(esk1_0,k2_lattices(esk1_0,X1,k7_lattices(esk1_0,esk3_0)),k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk3_0)))
    | ~ v7_lattices(esk1_0)
    | ~ r1_lattices(esk1_0,X1,esk3_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_31]),c_0_32])]),c_0_28])).

cnf(c_0_80,negated_conjecture,
    ( k2_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) = k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))
    | ~ v6_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_31])).

cnf(c_0_81,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,esk3_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_27]),c_0_73])])).

cnf(c_0_82,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,X1),esk3_0) = k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,X1))
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_31]),c_0_32])]),c_0_28])).

cnf(c_0_83,negated_conjecture,
    ( ~ v13_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ r1_lattices(esk1_0,k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0),k5_lattices(esk1_0))
    | ~ l2_lattices(esk1_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_28]),c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0) = k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))
    | ~ v6_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_31])).

cnf(c_0_85,negated_conjecture,
    ( r1_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk3_0)))
    | ~ v7_lattices(esk1_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_27])]),c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk3_0)) = k5_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_31]),c_0_44])).

cnf(c_0_87,negated_conjecture,
    ( ~ v13_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ r1_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),k5_lattices(esk1_0))
    | ~ l2_lattices(esk1_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( r1_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),k5_lattices(esk1_0))
    | ~ v7_lattices(esk1_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( ~ v13_lattices(esk1_0)
    | ~ v7_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ l2_lattices(esk1_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

fof(c_0_90,plain,(
    ! [X84] :
      ( ( ~ v2_struct_0(X84)
        | v2_struct_0(X84)
        | ~ v15_lattices(X84)
        | ~ l3_lattices(X84) )
      & ( v13_lattices(X84)
        | v2_struct_0(X84)
        | ~ v15_lattices(X84)
        | ~ l3_lattices(X84) )
      & ( v14_lattices(X84)
        | v2_struct_0(X84)
        | ~ v15_lattices(X84)
        | ~ l3_lattices(X84) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_lattices])])])])).

cnf(c_0_91,negated_conjecture,
    ( ~ v13_lattices(esk1_0)
    | ~ v7_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ l2_lattices(esk1_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_36]),c_0_31]),c_0_32])]),c_0_28])).

cnf(c_0_92,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( ~ v15_lattices(esk1_0)
    | ~ v7_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ l2_lattices(esk1_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_32])]),c_0_28])).

cnf(c_0_94,plain,
    ( v7_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_95,negated_conjecture,
    ( ~ v15_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ l2_lattices(esk1_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_32]),c_0_34])]),c_0_28])).

cnf(c_0_96,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_97,plain,(
    ! [X85] :
      ( ( ~ v2_struct_0(X85)
        | v2_struct_0(X85)
        | ~ v17_lattices(X85)
        | ~ l3_lattices(X85) )
      & ( v11_lattices(X85)
        | v2_struct_0(X85)
        | ~ v17_lattices(X85)
        | ~ l3_lattices(X85) )
      & ( v15_lattices(X85)
        | v2_struct_0(X85)
        | ~ v17_lattices(X85)
        | ~ l3_lattices(X85) )
      & ( v16_lattices(X85)
        | v2_struct_0(X85)
        | ~ v17_lattices(X85)
        | ~ l3_lattices(X85) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_lattices])])])])).

cnf(c_0_98,negated_conjecture,
    ( ~ v15_lattices(esk1_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ l2_lattices(esk1_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_32]),c_0_34])]),c_0_28])).

cnf(c_0_99,plain,
    ( v15_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ l2_lattices(esk1_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_32]),c_0_33])]),c_0_28])).

cnf(c_0_101,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_102,negated_conjecture,
    ( ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_32])])).

cnf(c_0_103,negated_conjecture,
    ( ~ v8_lattices(esk1_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_54]),c_0_32]),c_0_34])]),c_0_28])).

cnf(c_0_104,negated_conjecture,
    ( ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_53]),c_0_32]),c_0_34])]),c_0_28])).

cnf(c_0_105,negated_conjecture,
    ( ~ l1_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_52]),c_0_32]),c_0_34])]),c_0_28])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_37]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
