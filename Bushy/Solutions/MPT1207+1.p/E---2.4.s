%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattices__t41_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:02 EDT 2019

% Result     : Theorem 0.51s
% Output     : CNFRefutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 256 expanded)
%              Number of clauses        :   37 (  83 expanded)
%              Number of leaves         :    8 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  249 (1401 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r3_lattices(X1,k5_lattices(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',t41_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',t22_lattices)).

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',redefinition_k3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',cc1_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',dt_l3_lattices)).

fof(t39_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k3_lattices(X1,k5_lattices(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',t39_lattices)).

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',dt_k5_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',redefinition_r3_lattices)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v13_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => r3_lattices(X1,k5_lattices(X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t41_lattices])).

fof(c_0_9,plain,(
    ! [X51,X52,X53] :
      ( v2_struct_0(X51)
      | ~ v5_lattices(X51)
      | ~ v6_lattices(X51)
      | ~ v8_lattices(X51)
      | ~ v9_lattices(X51)
      | ~ l3_lattices(X51)
      | ~ m1_subset_1(X52,u1_struct_0(X51))
      | ~ m1_subset_1(X53,u1_struct_0(X51))
      | r1_lattices(X51,X52,k1_lattices(X51,X52,X53)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_lattices])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v13_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ~ r3_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X36,X37,X38] :
      ( v2_struct_0(X36)
      | ~ v4_lattices(X36)
      | ~ l2_lattices(X36)
      | ~ m1_subset_1(X37,u1_struct_0(X36))
      | ~ m1_subset_1(X38,u1_struct_0(X36))
      | k3_lattices(X36,X37,X38) = k1_lattices(X36,X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

cnf(c_0_12,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,X2,k1_lattices(X1,X2,X3))
    | ~ v5_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X71] :
      ( ( ~ v2_struct_0(X71)
        | v2_struct_0(X71)
        | ~ v10_lattices(X71)
        | ~ l3_lattices(X71) )
      & ( v4_lattices(X71)
        | v2_struct_0(X71)
        | ~ v10_lattices(X71)
        | ~ l3_lattices(X71) )
      & ( v5_lattices(X71)
        | v2_struct_0(X71)
        | ~ v10_lattices(X71)
        | ~ l3_lattices(X71) )
      & ( v6_lattices(X71)
        | v2_struct_0(X71)
        | ~ v10_lattices(X71)
        | ~ l3_lattices(X71) )
      & ( v7_lattices(X71)
        | v2_struct_0(X71)
        | ~ v10_lattices(X71)
        | ~ l3_lattices(X71) )
      & ( v8_lattices(X71)
        | v2_struct_0(X71)
        | ~ v10_lattices(X71)
        | ~ l3_lattices(X71) )
      & ( v9_lattices(X71)
        | v2_struct_0(X71)
        | ~ v10_lattices(X71)
        | ~ l3_lattices(X71) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r1_lattices(esk1_0,X1,k1_lattices(esk1_0,X1,esk2_0))
    | ~ v5_lattices(esk1_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_19,plain,
    ( v5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( k1_lattices(esk1_0,X1,esk2_0) = k3_lattices(esk1_0,X1,esk2_0)
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_15])).

cnf(c_0_22,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X28] :
      ( ( l1_lattices(X28)
        | ~ l3_lattices(X28) )
      & ( l2_lattices(X28)
        | ~ l3_lattices(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_24,plain,(
    ! [X56,X57] :
      ( v2_struct_0(X56)
      | ~ v10_lattices(X56)
      | ~ v13_lattices(X56)
      | ~ l3_lattices(X56)
      | ~ m1_subset_1(X57,u1_struct_0(X56))
      | k3_lattices(X56,k5_lattices(X56),X57) = X57 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_lattices])])])])).

cnf(c_0_25,negated_conjecture,
    ( r1_lattices(esk1_0,X1,k1_lattices(esk1_0,X1,esk2_0))
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_14]),c_0_20])]),c_0_15])).

cnf(c_0_26,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( k1_lattices(esk1_0,X1,esk2_0) = k3_lattices(esk1_0,X1,esk2_0)
    | ~ l2_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_14]),c_0_20])]),c_0_15])).

cnf(c_0_28,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X25] :
      ( v2_struct_0(X25)
      | ~ l1_lattices(X25)
      | m1_subset_1(k5_lattices(X25),u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,k5_lattices(X1),X2) = X2
    | ~ v10_lattices(X1)
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( v13_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( r1_lattices(esk1_0,X1,k1_lattices(esk1_0,X1,esk2_0))
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_14]),c_0_20])]),c_0_15])).

cnf(c_0_33,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( k1_lattices(esk1_0,X1,esk2_0) = k3_lattices(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_14])])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k3_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_13]),c_0_14]),c_0_31]),c_0_20])]),c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( r1_lattices(esk1_0,X1,k1_lattices(esk1_0,X1,esk2_0))
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_14]),c_0_20])]),c_0_15])).

cnf(c_0_38,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_39,negated_conjecture,
    ( k1_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) = esk2_0
    | ~ l1_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_15])).

cnf(c_0_40,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( r1_lattices(esk1_0,X1,k1_lattices(esk1_0,X1,esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_14]),c_0_20])]),c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( k1_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_14])])).

fof(c_0_43,plain,(
    ! [X43,X44,X45] :
      ( ( ~ r3_lattices(X43,X44,X45)
        | r1_lattices(X43,X44,X45)
        | v2_struct_0(X43)
        | ~ v6_lattices(X43)
        | ~ v8_lattices(X43)
        | ~ v9_lattices(X43)
        | ~ l3_lattices(X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ m1_subset_1(X45,u1_struct_0(X43)) )
      & ( ~ r1_lattices(X43,X44,X45)
        | r3_lattices(X43,X44,X45)
        | v2_struct_0(X43)
        | ~ v6_lattices(X43)
        | ~ v8_lattices(X43)
        | ~ v9_lattices(X43)
        | ~ l3_lattices(X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ m1_subset_1(X45,u1_struct_0(X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_44,negated_conjecture,
    ( r1_lattices(esk1_0,k5_lattices(esk1_0),esk2_0)
    | ~ l1_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_35]),c_0_42]),c_0_15])).

cnf(c_0_45,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( r1_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_40]),c_0_14])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r3_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_48,negated_conjecture,
    ( ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(k5_lattices(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_13]),c_0_14])]),c_0_47]),c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(k5_lattices(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_26]),c_0_14]),c_0_20])]),c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(k5_lattices(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_33]),c_0_14]),c_0_20])]),c_0_15])).

cnf(c_0_51,negated_conjecture,
    ( ~ m1_subset_1(k5_lattices(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_38]),c_0_14]),c_0_20])]),c_0_15])).

cnf(c_0_52,negated_conjecture,
    ( ~ l1_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_35]),c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_40]),c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
