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
% DateTime   : Thu Dec  3 11:14:50 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 726 expanded)
%              Number of clauses        :   66 ( 242 expanded)
%              Number of leaves         :    8 ( 179 expanded)
%              Depth                    :   15
%              Number of atoms          :  339 (4410 expanded)
%              Number of equality atoms :   46 ( 845 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_filter_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( k2_filter_0(X1,X2) = k2_filter_0(X1,X3)
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_filter_1)).

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

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

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

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(commutativity_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

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

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( k2_filter_0(X1,X2) = k2_filter_0(X1,X3)
                 => X2 = X3 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t2_filter_1])).

fof(c_0_9,plain,(
    ! [X18,X19,X20] :
      ( v2_struct_0(X18)
      | ~ v6_lattices(X18)
      | ~ v8_lattices(X18)
      | ~ v9_lattices(X18)
      | ~ l3_lattices(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | r3_lattices(X18,X19,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_lattices])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & k2_filter_0(esk1_0,esk2_0) = k2_filter_0(esk1_0,esk3_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,X2,X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( r3_lattices(esk1_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])]),c_0_14]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

fof(c_0_17,plain,(
    ! [X4] :
      ( ( ~ v2_struct_0(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v4_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v5_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v6_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v7_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v8_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v9_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_18,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk2_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( r3_lattices(esk1_0,esk3_0,esk3_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_12])).

fof(c_0_22,plain,(
    ! [X12,X13,X14] :
      ( v2_struct_0(X12)
      | ~ v4_lattices(X12)
      | ~ l2_lattices(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | k3_lattices(X12,X13,X14) = k1_lattices(X12,X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

cnf(c_0_23,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk2_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_13])]),c_0_14])).

cnf(c_0_24,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( r3_lattices(esk1_0,esk3_0,esk3_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_19]),c_0_20]),c_0_13])]),c_0_14])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

fof(c_0_27,plain,(
    ! [X15,X16,X17] :
      ( ( ~ r3_lattices(X15,X16,X17)
        | r1_lattices(X15,X16,X17)
        | v2_struct_0(X15)
        | ~ v6_lattices(X15)
        | ~ v8_lattices(X15)
        | ~ v9_lattices(X15)
        | ~ l3_lattices(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15)) )
      & ( ~ r1_lattices(X15,X16,X17)
        | r3_lattices(X15,X16,X17)
        | v2_struct_0(X15)
        | ~ v6_lattices(X15)
        | ~ v8_lattices(X15)
        | ~ v9_lattices(X15)
        | ~ l3_lattices(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_28,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk2_0)
    | ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_20]),c_0_13])]),c_0_14])).

cnf(c_0_29,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( r3_lattices(esk1_0,esk3_0,esk3_0)
    | ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_20]),c_0_13])]),c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( k3_lattices(esk1_0,X1,esk3_0) = k1_lattices(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_12]),c_0_14]),
    [final]).

fof(c_0_32,plain,(
    ! [X11] :
      ( ( l1_lattices(X11)
        | ~ l3_lattices(X11) )
      & ( l2_lattices(X11)
        | ~ l3_lattices(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_33,negated_conjecture,
    ( k3_lattices(esk1_0,X1,esk2_0) = k1_lattices(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_16]),c_0_14]),
    [final]).

cnf(c_0_34,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_20]),c_0_13])]),c_0_14]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( r3_lattices(esk1_0,esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_20]),c_0_13])]),c_0_14]),
    [final]).

fof(c_0_37,plain,(
    ! [X5,X6,X7] :
      ( v2_struct_0(X5)
      | ~ v4_lattices(X5)
      | ~ l2_lattices(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | k3_lattices(X5,X6,X7) = k3_lattices(X5,X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).

cnf(c_0_38,negated_conjecture,
    ( k3_lattices(esk1_0,esk2_0,esk3_0) = k1_lattices(esk1_0,esk2_0,esk3_0)
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_16])).

cnf(c_0_39,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( k3_lattices(esk1_0,esk3_0,esk2_0) = k1_lattices(esk1_0,esk3_0,esk2_0)
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,esk2_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_16]),c_0_13])]),c_0_14])).

cnf(c_0_42,negated_conjecture,
    ( r1_lattices(esk1_0,esk3_0,esk3_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_36]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( k3_lattices(esk1_0,esk2_0,esk3_0) = k1_lattices(esk1_0,esk2_0,esk3_0)
    | ~ v4_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_13])])).

cnf(c_0_45,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( k3_lattices(esk1_0,esk3_0,esk2_0) = k1_lattices(esk1_0,esk3_0,esk2_0)
    | ~ v4_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_39]),c_0_13])])).

cnf(c_0_47,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,esk2_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_19]),c_0_20]),c_0_13])]),c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( r1_lattices(esk1_0,esk3_0,esk3_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_19]),c_0_20]),c_0_13])]),c_0_14])).

cnf(c_0_49,negated_conjecture,
    ( k3_lattices(esk1_0,X1,esk3_0) = k3_lattices(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_12]),c_0_14]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( k3_lattices(esk1_0,esk2_0,esk3_0) = k1_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_20]),c_0_13])]),c_0_14]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( k3_lattices(esk1_0,esk3_0,esk2_0) = k1_lattices(esk1_0,esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_45]),c_0_20]),c_0_13])]),c_0_14])).

fof(c_0_52,plain,(
    ! [X8,X9,X10] :
      ( ( ~ r1_lattices(X8,X9,X10)
        | k1_lattices(X8,X9,X10) = X10
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ l2_lattices(X8) )
      & ( k1_lattices(X8,X9,X10) != X10
        | r1_lattices(X8,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ l2_lattices(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

cnf(c_0_53,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,esk2_0)
    | ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_24]),c_0_20]),c_0_13])]),c_0_14])).

cnf(c_0_54,negated_conjecture,
    ( r1_lattices(esk1_0,esk3_0,esk3_0)
    | ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_24]),c_0_20]),c_0_13])]),c_0_14])).

cnf(c_0_55,negated_conjecture,
    ( k1_lattices(esk1_0,esk3_0,esk2_0) = k1_lattices(esk1_0,esk2_0,esk3_0)
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_16]),c_0_50]),c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( k3_lattices(esk1_0,esk2_0,esk2_0) = k1_lattices(esk1_0,esk2_0,esk2_0)
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_16])).

cnf(c_0_57,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_29]),c_0_20]),c_0_13])]),c_0_14]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( k3_lattices(esk1_0,esk3_0,esk3_0) = k1_lattices(esk1_0,esk3_0,esk3_0)
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_12])).

cnf(c_0_60,negated_conjecture,
    ( r1_lattices(esk1_0,esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_29]),c_0_20]),c_0_13])]),c_0_14]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( k1_lattices(esk1_0,esk3_0,esk2_0) = k1_lattices(esk1_0,esk2_0,esk3_0)
    | ~ v4_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_39]),c_0_13])])).

cnf(c_0_62,negated_conjecture,
    ( k3_lattices(esk1_0,esk2_0,esk2_0) = k1_lattices(esk1_0,esk2_0,esk2_0)
    | ~ v4_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_39]),c_0_13])])).

cnf(c_0_63,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,esk2_0) = esk2_0
    | ~ l2_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_16])]),c_0_14])).

cnf(c_0_64,negated_conjecture,
    ( k3_lattices(esk1_0,esk3_0,esk3_0) = k1_lattices(esk1_0,esk3_0,esk3_0)
    | ~ v4_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_39]),c_0_13])])).

cnf(c_0_65,negated_conjecture,
    ( k1_lattices(esk1_0,esk3_0,esk3_0) = esk3_0
    | ~ l2_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_60]),c_0_12])]),c_0_14])).

cnf(c_0_66,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( k1_lattices(esk1_0,esk3_0,esk2_0) = k1_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_45]),c_0_20]),c_0_13])]),c_0_14]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( k3_lattices(esk1_0,esk2_0,esk2_0) = k1_lattices(esk1_0,esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_45]),c_0_20]),c_0_13])]),c_0_14])).

cnf(c_0_69,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_39]),c_0_13])]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( k3_lattices(esk1_0,esk3_0,esk3_0) = k1_lattices(esk1_0,esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_45]),c_0_20]),c_0_13])]),c_0_14])).

cnf(c_0_71,negated_conjecture,
    ( k1_lattices(esk1_0,esk3_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_39]),c_0_13])]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( k3_lattices(esk1_0,X1,esk2_0) = k3_lattices(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_16]),c_0_14]),
    [final]).

cnf(c_0_73,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( r1_lattices(esk1_0,esk3_0,esk2_0)
    | k1_lattices(esk1_0,esk2_0,esk3_0) != esk2_0
    | ~ l2_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_16]),c_0_12])]),c_0_14]),
    [final]).

cnf(c_0_75,plain,
    ( v7_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_76,plain,
    ( v5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_77,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( k3_lattices(esk1_0,esk2_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_68,c_0_69]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( k3_lattices(esk1_0,esk3_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_70,c_0_71]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( k3_lattices(esk1_0,esk3_0,esk2_0) = k1_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_67]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( k2_filter_0(esk1_0,esk2_0) = k2_filter_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:17:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.14/0.38  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # No proof found!
% 0.14/0.38  # SZS status CounterSatisfiable
% 0.14/0.38  # SZS output start Saturation
% 0.14/0.38  fof(t2_filter_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_filter_0(X1,X2)=k2_filter_0(X1,X3)=>X2=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_filter_1)).
% 0.14/0.38  fof(reflexivity_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_lattices(X1,X2,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_lattices)).
% 0.14/0.38  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.14/0.38  fof(redefinition_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 0.14/0.38  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.14/0.38  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.14/0.38  fof(commutativity_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 0.14/0.38  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_filter_0(X1,X2)=k2_filter_0(X1,X3)=>X2=X3))))), inference(assume_negation,[status(cth)],[t2_filter_1])).
% 0.14/0.38  fof(c_0_9, plain, ![X18, X19, X20]:(v2_struct_0(X18)|~v6_lattices(X18)|~v8_lattices(X18)|~v9_lattices(X18)|~l3_lattices(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|r3_lattices(X18,X19,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_lattices])])])).
% 0.14/0.38  fof(c_0_10, negated_conjecture, (((~v2_struct_0(esk1_0)&v10_lattices(esk1_0))&l3_lattices(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(m1_subset_1(esk3_0,u1_struct_0(esk1_0))&(k2_filter_0(esk1_0,esk2_0)=k2_filter_0(esk1_0,esk3_0)&esk2_0!=esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.14/0.38  cnf(c_0_11, plain, (v2_struct_0(X1)|r3_lattices(X1,X2,X2)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (l3_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (r3_lattices(esk1_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)|~v6_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])]), c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.38  fof(c_0_17, plain, ![X4]:(((((((~v2_struct_0(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))&(v4_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v5_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v6_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v7_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v8_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v9_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (r3_lattices(esk1_0,esk2_0,esk2_0)|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)|~v6_lattices(esk1_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.38  cnf(c_0_19, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (v10_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (r3_lattices(esk1_0,esk3_0,esk3_0)|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)|~v6_lattices(esk1_0)), inference(spm,[status(thm)],[c_0_15, c_0_12])).
% 0.14/0.38  fof(c_0_22, plain, ![X12, X13, X14]:(v2_struct_0(X12)|~v4_lattices(X12)|~l2_lattices(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))|k3_lattices(X12,X13,X14)=k1_lattices(X12,X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (r3_lattices(esk1_0,esk2_0,esk2_0)|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_13])]), c_0_14])).
% 0.14/0.38  cnf(c_0_24, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (r3_lattices(esk1_0,esk3_0,esk3_0)|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_19]), c_0_20]), c_0_13])]), c_0_14])).
% 0.14/0.38  cnf(c_0_26, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.14/0.38  fof(c_0_27, plain, ![X15, X16, X17]:((~r3_lattices(X15,X16,X17)|r1_lattices(X15,X16,X17)|(v2_struct_0(X15)|~v6_lattices(X15)|~v8_lattices(X15)|~v9_lattices(X15)|~l3_lattices(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))))&(~r1_lattices(X15,X16,X17)|r3_lattices(X15,X16,X17)|(v2_struct_0(X15)|~v6_lattices(X15)|~v8_lattices(X15)|~v9_lattices(X15)|~l3_lattices(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (r3_lattices(esk1_0,esk2_0,esk2_0)|~v9_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_20]), c_0_13])]), c_0_14])).
% 0.14/0.38  cnf(c_0_29, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (r3_lattices(esk1_0,esk3_0,esk3_0)|~v9_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_24]), c_0_20]), c_0_13])]), c_0_14])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (k3_lattices(esk1_0,X1,esk3_0)=k1_lattices(esk1_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~l2_lattices(esk1_0)|~v4_lattices(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_12]), c_0_14]), ['final']).
% 0.14/0.38  fof(c_0_32, plain, ![X11]:((l1_lattices(X11)|~l3_lattices(X11))&(l2_lattices(X11)|~l3_lattices(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (k3_lattices(esk1_0,X1,esk2_0)=k1_lattices(esk1_0,X1,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~l2_lattices(esk1_0)|~v4_lattices(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_16]), c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_34, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (r3_lattices(esk1_0,esk2_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_20]), c_0_13])]), c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (r3_lattices(esk1_0,esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_29]), c_0_20]), c_0_13])]), c_0_14]), ['final']).
% 0.14/0.38  fof(c_0_37, plain, ![X5, X6, X7]:(v2_struct_0(X5)|~v4_lattices(X5)|~l2_lattices(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))|k3_lattices(X5,X6,X7)=k3_lattices(X5,X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (k3_lattices(esk1_0,esk2_0,esk3_0)=k1_lattices(esk1_0,esk2_0,esk3_0)|~l2_lattices(esk1_0)|~v4_lattices(esk1_0)), inference(spm,[status(thm)],[c_0_31, c_0_16])).
% 0.14/0.38  cnf(c_0_39, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (k3_lattices(esk1_0,esk3_0,esk2_0)=k1_lattices(esk1_0,esk3_0,esk2_0)|~l2_lattices(esk1_0)|~v4_lattices(esk1_0)), inference(spm,[status(thm)],[c_0_33, c_0_12])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (r1_lattices(esk1_0,esk2_0,esk2_0)|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)|~v6_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_16]), c_0_13])]), c_0_14])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (r1_lattices(esk1_0,esk3_0,esk3_0)|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)|~v6_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_36]), c_0_12]), c_0_13])]), c_0_14])).
% 0.14/0.38  cnf(c_0_43, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (k3_lattices(esk1_0,esk2_0,esk3_0)=k1_lattices(esk1_0,esk2_0,esk3_0)|~v4_lattices(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_13])])).
% 0.14/0.38  cnf(c_0_45, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (k3_lattices(esk1_0,esk3_0,esk2_0)=k1_lattices(esk1_0,esk3_0,esk2_0)|~v4_lattices(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_39]), c_0_13])])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (r1_lattices(esk1_0,esk2_0,esk2_0)|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_19]), c_0_20]), c_0_13])]), c_0_14])).
% 0.14/0.38  cnf(c_0_48, negated_conjecture, (r1_lattices(esk1_0,esk3_0,esk3_0)|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_19]), c_0_20]), c_0_13])]), c_0_14])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (k3_lattices(esk1_0,X1,esk3_0)=k3_lattices(esk1_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~l2_lattices(esk1_0)|~v4_lattices(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_12]), c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (k3_lattices(esk1_0,esk2_0,esk3_0)=k1_lattices(esk1_0,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_20]), c_0_13])]), c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (k3_lattices(esk1_0,esk3_0,esk2_0)=k1_lattices(esk1_0,esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_45]), c_0_20]), c_0_13])]), c_0_14])).
% 0.14/0.38  fof(c_0_52, plain, ![X8, X9, X10]:((~r1_lattices(X8,X9,X10)|k1_lattices(X8,X9,X10)=X10|~m1_subset_1(X10,u1_struct_0(X8))|~m1_subset_1(X9,u1_struct_0(X8))|(v2_struct_0(X8)|~l2_lattices(X8)))&(k1_lattices(X8,X9,X10)!=X10|r1_lattices(X8,X9,X10)|~m1_subset_1(X10,u1_struct_0(X8))|~m1_subset_1(X9,u1_struct_0(X8))|(v2_struct_0(X8)|~l2_lattices(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, (r1_lattices(esk1_0,esk2_0,esk2_0)|~v9_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_24]), c_0_20]), c_0_13])]), c_0_14])).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (r1_lattices(esk1_0,esk3_0,esk3_0)|~v9_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_24]), c_0_20]), c_0_13])]), c_0_14])).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (k1_lattices(esk1_0,esk3_0,esk2_0)=k1_lattices(esk1_0,esk2_0,esk3_0)|~l2_lattices(esk1_0)|~v4_lattices(esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_16]), c_0_50]), c_0_51])).
% 0.14/0.38  cnf(c_0_56, negated_conjecture, (k3_lattices(esk1_0,esk2_0,esk2_0)=k1_lattices(esk1_0,esk2_0,esk2_0)|~l2_lattices(esk1_0)|~v4_lattices(esk1_0)), inference(spm,[status(thm)],[c_0_33, c_0_16])).
% 0.14/0.38  cnf(c_0_57, plain, (k1_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_52]), ['final']).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, (r1_lattices(esk1_0,esk2_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_29]), c_0_20]), c_0_13])]), c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, (k3_lattices(esk1_0,esk3_0,esk3_0)=k1_lattices(esk1_0,esk3_0,esk3_0)|~l2_lattices(esk1_0)|~v4_lattices(esk1_0)), inference(spm,[status(thm)],[c_0_31, c_0_12])).
% 0.14/0.38  cnf(c_0_60, negated_conjecture, (r1_lattices(esk1_0,esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_29]), c_0_20]), c_0_13])]), c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_61, negated_conjecture, (k1_lattices(esk1_0,esk3_0,esk2_0)=k1_lattices(esk1_0,esk2_0,esk3_0)|~v4_lattices(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_39]), c_0_13])])).
% 0.14/0.38  cnf(c_0_62, negated_conjecture, (k3_lattices(esk1_0,esk2_0,esk2_0)=k1_lattices(esk1_0,esk2_0,esk2_0)|~v4_lattices(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_39]), c_0_13])])).
% 0.14/0.38  cnf(c_0_63, negated_conjecture, (k1_lattices(esk1_0,esk2_0,esk2_0)=esk2_0|~l2_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_16])]), c_0_14])).
% 0.14/0.38  cnf(c_0_64, negated_conjecture, (k3_lattices(esk1_0,esk3_0,esk3_0)=k1_lattices(esk1_0,esk3_0,esk3_0)|~v4_lattices(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_39]), c_0_13])])).
% 0.14/0.38  cnf(c_0_65, negated_conjecture, (k1_lattices(esk1_0,esk3_0,esk3_0)=esk3_0|~l2_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_60]), c_0_12])]), c_0_14])).
% 0.14/0.38  cnf(c_0_66, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k1_lattices(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_52]), ['final']).
% 0.14/0.38  cnf(c_0_67, negated_conjecture, (k1_lattices(esk1_0,esk3_0,esk2_0)=k1_lattices(esk1_0,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_45]), c_0_20]), c_0_13])]), c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_68, negated_conjecture, (k3_lattices(esk1_0,esk2_0,esk2_0)=k1_lattices(esk1_0,esk2_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_45]), c_0_20]), c_0_13])]), c_0_14])).
% 0.14/0.38  cnf(c_0_69, negated_conjecture, (k1_lattices(esk1_0,esk2_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_39]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_70, negated_conjecture, (k3_lattices(esk1_0,esk3_0,esk3_0)=k1_lattices(esk1_0,esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_45]), c_0_20]), c_0_13])]), c_0_14])).
% 0.14/0.38  cnf(c_0_71, negated_conjecture, (k1_lattices(esk1_0,esk3_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_39]), c_0_13])]), ['final']).
% 0.14/0.38  cnf(c_0_72, negated_conjecture, (k3_lattices(esk1_0,X1,esk2_0)=k3_lattices(esk1_0,esk2_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~l2_lattices(esk1_0)|~v4_lattices(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_16]), c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_73, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.14/0.38  cnf(c_0_74, negated_conjecture, (r1_lattices(esk1_0,esk3_0,esk2_0)|k1_lattices(esk1_0,esk2_0,esk3_0)!=esk2_0|~l2_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_16]), c_0_12])]), c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_75, plain, (v7_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.14/0.38  cnf(c_0_76, plain, (v5_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.14/0.38  cnf(c_0_77, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.14/0.38  cnf(c_0_78, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_79, negated_conjecture, (k3_lattices(esk1_0,esk2_0,esk2_0)=esk2_0), inference(rw,[status(thm)],[c_0_68, c_0_69]), ['final']).
% 0.14/0.38  cnf(c_0_80, negated_conjecture, (k3_lattices(esk1_0,esk3_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[c_0_70, c_0_71]), ['final']).
% 0.14/0.38  cnf(c_0_81, negated_conjecture, (k3_lattices(esk1_0,esk3_0,esk2_0)=k1_lattices(esk1_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_51, c_0_67]), ['final']).
% 0.14/0.38  cnf(c_0_82, negated_conjecture, (k2_filter_0(esk1_0,esk2_0)=k2_filter_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.38  # SZS output end Saturation
% 0.14/0.38  # Proof object total steps             : 83
% 0.14/0.38  # Proof object clause steps            : 66
% 0.14/0.38  # Proof object formula steps           : 17
% 0.14/0.38  # Proof object conjectures             : 54
% 0.14/0.38  # Proof object clause conjectures      : 51
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 22
% 0.14/0.38  # Proof object initial formulas used   : 8
% 0.14/0.38  # Proof object generating inferences   : 41
% 0.14/0.38  # Proof object simplifying inferences  : 112
% 0.14/0.38  # Parsed axioms                        : 8
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 23
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 22
% 0.14/0.38  # Processed clauses                    : 89
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 1
% 0.14/0.38  # ...remaining for further processing  : 88
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 13
% 0.14/0.38  # Backward-rewritten                   : 14
% 0.14/0.38  # Generated clauses                    : 47
% 0.14/0.38  # ...of the previous two non-trivial   : 45
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 47
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 39
% 0.14/0.38  #    Positive orientable unit clauses  : 16
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 21
% 0.14/0.38  # Current number of unprocessed clauses: 0
% 0.14/0.38  # ...number of literals in the above   : 0
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 49
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 290
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 92
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 14
% 0.14/0.38  # Unit Clause-clause subsumption calls : 5
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 22
% 0.14/0.38  # BW rewrite match successes           : 11
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 3344
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.033 s
% 0.14/0.38  # System time              : 0.002 s
% 0.14/0.38  # Total time               : 0.035 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
