%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:29 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 (1208 expanded)
%              Number of clauses        :   51 ( 392 expanded)
%              Number of leaves         :   11 ( 297 expanded)
%              Depth                    :   14
%              Number of atoms          :  352 (7976 expanded)
%              Number of equality atoms :   34 ( 100 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

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

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattices)).

fof(dt_k7_lattices,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

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

fof(commutativity_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X13] :
      ( ( l1_lattices(X13)
        | ~ l3_lattices(X13) )
      & ( l2_lattices(X13)
        | ~ l3_lattices(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v17_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & r3_lattices(esk1_0,esk2_0,esk3_0)
    & ~ r3_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
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

fof(c_0_15,plain,(
    ! [X17,X18,X19] :
      ( v2_struct_0(X17)
      | ~ v6_lattices(X17)
      | ~ l1_lattices(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | k4_lattices(X17,X18,X19) = k2_lattices(X17,X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

cnf(c_0_16,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X23,X24,X25] :
      ( ( ~ r1_lattices(X23,X24,X25)
        | k2_lattices(X23,X24,X25) = X24
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v8_lattices(X23)
        | ~ v9_lattices(X23)
        | ~ l3_lattices(X23) )
      & ( k2_lattices(X23,X24,X25) != X24
        | r1_lattices(X23,X24,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v8_lattices(X23)
        | ~ v9_lattices(X23)
        | ~ l3_lattices(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_22,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_24,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r3_lattices(X20,X21,X22)
        | r1_lattices(X20,X21,X22)
        | v2_struct_0(X20)
        | ~ v6_lattices(X20)
        | ~ v8_lattices(X20)
        | ~ v9_lattices(X20)
        | ~ l3_lattices(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20)) )
      & ( ~ r1_lattices(X20,X21,X22)
        | r3_lattices(X20,X21,X22)
        | v2_struct_0(X20)
        | ~ v6_lattices(X20)
        | ~ v8_lattices(X20)
        | ~ v9_lattices(X20)
        | ~ l3_lattices(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( l1_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_17])]),c_0_20])).

cnf(c_0_29,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_17])]),c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_17])]),c_0_20])).

cnf(c_0_32,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_35,plain,(
    ! [X26,X27,X28] :
      ( v2_struct_0(X26)
      | ~ v10_lattices(X26)
      | ~ v17_lattices(X26)
      | ~ l3_lattices(X26)
      | ~ m1_subset_1(X27,u1_struct_0(X26))
      | ~ m1_subset_1(X28,u1_struct_0(X26))
      | k7_lattices(X26,k4_lattices(X26,X27,X28)) = k3_lattices(X26,k7_lattices(X26,X27),k7_lattices(X26,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_lattices])])])])).

cnf(c_0_36,negated_conjecture,
    ( k4_lattices(esk1_0,X1,esk3_0) = k2_lattices(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_20]),c_0_27]),c_0_28])])).

cnf(c_0_37,negated_conjecture,
    ( k2_lattices(esk1_0,X1,esk3_0) = X1
    | ~ r1_lattices(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_26]),c_0_17])]),c_0_20]),c_0_30]),c_0_31])])).

cnf(c_0_38,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_26]),c_0_34]),c_0_17])]),c_0_20]),c_0_30]),c_0_31]),c_0_28])])).

fof(c_0_39,plain,(
    ! [X11,X12] :
      ( v2_struct_0(X11)
      | ~ l3_lattices(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | m1_subset_1(k7_lattices(X11,X12),u1_struct_0(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | k7_lattices(X1,k4_lattices(X1,X2,X3)) = k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( k4_lattices(esk1_0,esk2_0,esk3_0) = k2_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k2_lattices(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_34]),c_0_38])])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( k7_lattices(esk1_0,k4_lattices(esk1_0,X1,X2)) = k3_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_19]),c_0_17])]),c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( k4_lattices(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_47,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ v4_lattices(X14)
      | ~ l2_lattices(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | k3_lattices(X14,X15,X16) = k1_lattices(X14,X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

fof(c_0_48,plain,(
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

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k3_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,X2)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,X1,X2),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_17])]),c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),k7_lattices(esk1_0,esk3_0)) = k7_lattices(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_26]),c_0_34])])).

cnf(c_0_51,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_53,plain,(
    ! [X5,X6,X7] :
      ( v2_struct_0(X5)
      | ~ v4_lattices(X5)
      | ~ l2_lattices(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | k3_lattices(X5,X6,X7) = k3_lattices(X5,X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).

cnf(c_0_54,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_46]),c_0_50]),c_0_34]),c_0_26])])).

cnf(c_0_56,negated_conjecture,
    ( l2_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_17])).

cnf(c_0_57,plain,
    ( k1_lattices(X1,X2,k7_lattices(X1,X3)) = k3_lattices(X1,X2,k7_lattices(X1,X3))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_44]),c_0_51])).

cnf(c_0_58,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( ~ r3_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_61,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_62,negated_conjecture,
    ( r1_lattices(esk1_0,X1,k7_lattices(esk1_0,esk2_0))
    | k1_lattices(esk1_0,X1,k7_lattices(esk1_0,esk2_0)) != k7_lattices(esk1_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])]),c_0_20])).

cnf(c_0_63,plain,
    ( k1_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3)) = k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_44])).

cnf(c_0_64,negated_conjecture,
    ( v4_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_19]),c_0_17])]),c_0_20])).

cnf(c_0_65,plain,
    ( k3_lattices(X1,X2,k7_lattices(X1,X3)) = k3_lattices(X1,k7_lattices(X1,X3),X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_44]),c_0_51])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0))
    | ~ m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_17])]),c_0_20]),c_0_30]),c_0_31]),c_0_28])])).

cnf(c_0_67,negated_conjecture,
    ( r1_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,esk2_0))
    | k3_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,esk2_0)) != k7_lattices(esk1_0,esk2_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_34]),c_0_64]),c_0_17])]),c_0_20])).

cnf(c_0_68,plain,
    ( k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3)) = k3_lattices(X1,k7_lattices(X1,X3),k7_lattices(X1,X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_44])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0))
    | ~ m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_44]),c_0_26]),c_0_17])]),c_0_20])).

cnf(c_0_70,negated_conjecture,
    ( r1_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,esk2_0))
    | k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),k7_lattices(esk1_0,X1)) != k7_lattices(esk1_0,esk2_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_34]),c_0_64]),c_0_17])]),c_0_20])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_55])])).

cnf(c_0_72,negated_conjecture,
    ( ~ m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_50]),c_0_26])]),c_0_71])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_44]),c_0_26]),c_0_17])]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.49  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.19/0.49  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.49  #
% 0.19/0.49  # Preprocessing time       : 0.029 s
% 0.19/0.49  # Presaturation interreduction done
% 0.19/0.49  
% 0.19/0.49  # Proof found!
% 0.19/0.49  # SZS status Theorem
% 0.19/0.49  # SZS output start CNFRefutation
% 0.19/0.49  fof(t53_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_lattices(X1,X2,X3)=>r3_lattices(X1,k7_lattices(X1,X3),k7_lattices(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_lattices)).
% 0.19/0.49  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.19/0.49  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.19/0.49  fof(redefinition_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 0.19/0.49  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 0.19/0.49  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.19/0.49  fof(t50_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k7_lattices(X1,k4_lattices(X1,X2,X3))=k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_lattices)).
% 0.19/0.49  fof(dt_k7_lattices, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_lattices)).
% 0.19/0.49  fof(redefinition_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 0.19/0.49  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 0.19/0.49  fof(commutativity_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 0.19/0.49  fof(c_0_11, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_lattices(X1,X2,X3)=>r3_lattices(X1,k7_lattices(X1,X3),k7_lattices(X1,X2))))))), inference(assume_negation,[status(cth)],[t53_lattices])).
% 0.19/0.49  fof(c_0_12, plain, ![X13]:((l1_lattices(X13)|~l3_lattices(X13))&(l2_lattices(X13)|~l3_lattices(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.19/0.49  fof(c_0_13, negated_conjecture, ((((~v2_struct_0(esk1_0)&v10_lattices(esk1_0))&v17_lattices(esk1_0))&l3_lattices(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(m1_subset_1(esk3_0,u1_struct_0(esk1_0))&(r3_lattices(esk1_0,esk2_0,esk3_0)&~r3_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.19/0.49  fof(c_0_14, plain, ![X4]:(((((((~v2_struct_0(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))&(v4_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v5_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v6_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v7_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v8_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v9_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.19/0.49  fof(c_0_15, plain, ![X17, X18, X19]:(v2_struct_0(X17)|~v6_lattices(X17)|~l1_lattices(X17)|~m1_subset_1(X18,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|k4_lattices(X17,X18,X19)=k2_lattices(X17,X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).
% 0.19/0.49  cnf(c_0_16, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.49  cnf(c_0_17, negated_conjecture, (l3_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  cnf(c_0_18, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.49  cnf(c_0_19, negated_conjecture, (v10_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  fof(c_0_21, plain, ![X23, X24, X25]:((~r1_lattices(X23,X24,X25)|k2_lattices(X23,X24,X25)=X24|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v8_lattices(X23)|~v9_lattices(X23)|~l3_lattices(X23)))&(k2_lattices(X23,X24,X25)!=X24|r1_lattices(X23,X24,X25)|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v8_lattices(X23)|~v9_lattices(X23)|~l3_lattices(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.19/0.49  cnf(c_0_22, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.49  cnf(c_0_23, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.49  fof(c_0_24, plain, ![X20, X21, X22]:((~r3_lattices(X20,X21,X22)|r1_lattices(X20,X21,X22)|(v2_struct_0(X20)|~v6_lattices(X20)|~v8_lattices(X20)|~v9_lattices(X20)|~l3_lattices(X20)|~m1_subset_1(X21,u1_struct_0(X20))|~m1_subset_1(X22,u1_struct_0(X20))))&(~r1_lattices(X20,X21,X22)|r3_lattices(X20,X21,X22)|(v2_struct_0(X20)|~v6_lattices(X20)|~v8_lattices(X20)|~v9_lattices(X20)|~l3_lattices(X20)|~m1_subset_1(X21,u1_struct_0(X20))|~m1_subset_1(X22,u1_struct_0(X20))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.19/0.49  cnf(c_0_25, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.49  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  cnf(c_0_27, negated_conjecture, (l1_lattices(esk1_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.49  cnf(c_0_28, negated_conjecture, (v6_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_17])]), c_0_20])).
% 0.19/0.49  cnf(c_0_29, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.49  cnf(c_0_30, negated_conjecture, (v9_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_19]), c_0_17])]), c_0_20])).
% 0.19/0.49  cnf(c_0_31, negated_conjecture, (v8_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_19]), c_0_17])]), c_0_20])).
% 0.19/0.49  cnf(c_0_32, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.49  cnf(c_0_33, negated_conjecture, (r3_lattices(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  fof(c_0_35, plain, ![X26, X27, X28]:(v2_struct_0(X26)|~v10_lattices(X26)|~v17_lattices(X26)|~l3_lattices(X26)|(~m1_subset_1(X27,u1_struct_0(X26))|(~m1_subset_1(X28,u1_struct_0(X26))|k7_lattices(X26,k4_lattices(X26,X27,X28))=k3_lattices(X26,k7_lattices(X26,X27),k7_lattices(X26,X28))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_lattices])])])])).
% 0.19/0.49  cnf(c_0_36, negated_conjecture, (k4_lattices(esk1_0,X1,esk3_0)=k2_lattices(esk1_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_20]), c_0_27]), c_0_28])])).
% 0.19/0.49  cnf(c_0_37, negated_conjecture, (k2_lattices(esk1_0,X1,esk3_0)=X1|~r1_lattices(esk1_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_26]), c_0_17])]), c_0_20]), c_0_30]), c_0_31])])).
% 0.19/0.49  cnf(c_0_38, negated_conjecture, (r1_lattices(esk1_0,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_26]), c_0_34]), c_0_17])]), c_0_20]), c_0_30]), c_0_31]), c_0_28])])).
% 0.19/0.49  fof(c_0_39, plain, ![X11, X12]:(v2_struct_0(X11)|~l3_lattices(X11)|~m1_subset_1(X12,u1_struct_0(X11))|m1_subset_1(k7_lattices(X11,X12),u1_struct_0(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).
% 0.19/0.49  cnf(c_0_40, plain, (v2_struct_0(X1)|k7_lattices(X1,k4_lattices(X1,X2,X3))=k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))|~v10_lattices(X1)|~v17_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.49  cnf(c_0_41, negated_conjecture, (v17_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  cnf(c_0_42, negated_conjecture, (k4_lattices(esk1_0,esk2_0,esk3_0)=k2_lattices(esk1_0,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_34])).
% 0.19/0.49  cnf(c_0_43, negated_conjecture, (k2_lattices(esk1_0,esk2_0,esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_34]), c_0_38])])).
% 0.19/0.49  cnf(c_0_44, plain, (v2_struct_0(X1)|m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.49  cnf(c_0_45, negated_conjecture, (k7_lattices(esk1_0,k4_lattices(esk1_0,X1,X2))=k3_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,X2))|~m1_subset_1(X2,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_19]), c_0_17])]), c_0_20])).
% 0.19/0.49  cnf(c_0_46, negated_conjecture, (k4_lattices(esk1_0,esk2_0,esk3_0)=esk2_0), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.49  fof(c_0_47, plain, ![X14, X15, X16]:(v2_struct_0(X14)|~v4_lattices(X14)|~l2_lattices(X14)|~m1_subset_1(X15,u1_struct_0(X14))|~m1_subset_1(X16,u1_struct_0(X14))|k3_lattices(X14,X15,X16)=k1_lattices(X14,X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).
% 0.19/0.49  fof(c_0_48, plain, ![X8, X9, X10]:((~r1_lattices(X8,X9,X10)|k1_lattices(X8,X9,X10)=X10|~m1_subset_1(X10,u1_struct_0(X8))|~m1_subset_1(X9,u1_struct_0(X8))|(v2_struct_0(X8)|~l2_lattices(X8)))&(k1_lattices(X8,X9,X10)!=X10|r1_lattices(X8,X9,X10)|~m1_subset_1(X10,u1_struct_0(X8))|~m1_subset_1(X9,u1_struct_0(X8))|(v2_struct_0(X8)|~l2_lattices(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.19/0.49  cnf(c_0_49, negated_conjecture, (m1_subset_1(k3_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,X2)),u1_struct_0(esk1_0))|~m1_subset_1(k4_lattices(esk1_0,X1,X2),u1_struct_0(esk1_0))|~m1_subset_1(X2,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_17])]), c_0_20])).
% 0.19/0.49  cnf(c_0_50, negated_conjecture, (k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),k7_lattices(esk1_0,esk3_0))=k7_lattices(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_26]), c_0_34])])).
% 0.19/0.49  cnf(c_0_51, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.49  cnf(c_0_52, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.49  fof(c_0_53, plain, ![X5, X6, X7]:(v2_struct_0(X5)|~v4_lattices(X5)|~l2_lattices(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))|k3_lattices(X5,X6,X7)=k3_lattices(X5,X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).
% 0.19/0.49  cnf(c_0_54, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k1_lattices(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.49  cnf(c_0_55, negated_conjecture, (m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_46]), c_0_50]), c_0_34]), c_0_26])])).
% 0.19/0.49  cnf(c_0_56, negated_conjecture, (l2_lattices(esk1_0)), inference(spm,[status(thm)],[c_0_51, c_0_17])).
% 0.19/0.49  cnf(c_0_57, plain, (k1_lattices(X1,X2,k7_lattices(X1,X3))=k3_lattices(X1,X2,k7_lattices(X1,X3))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_44]), c_0_51])).
% 0.19/0.49  cnf(c_0_58, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.49  cnf(c_0_59, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.49  cnf(c_0_60, negated_conjecture, (~r3_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  cnf(c_0_61, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.49  cnf(c_0_62, negated_conjecture, (r1_lattices(esk1_0,X1,k7_lattices(esk1_0,esk2_0))|k1_lattices(esk1_0,X1,k7_lattices(esk1_0,esk2_0))!=k7_lattices(esk1_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])]), c_0_20])).
% 0.19/0.49  cnf(c_0_63, plain, (k1_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))=k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v4_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_57, c_0_44])).
% 0.19/0.49  cnf(c_0_64, negated_conjecture, (v4_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_19]), c_0_17])]), c_0_20])).
% 0.19/0.49  cnf(c_0_65, plain, (k3_lattices(X1,X2,k7_lattices(X1,X3))=k3_lattices(X1,k7_lattices(X1,X3),X2)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_44]), c_0_51])).
% 0.19/0.49  cnf(c_0_66, negated_conjecture, (~r1_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0))|~m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0))|~m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_17])]), c_0_20]), c_0_30]), c_0_31]), c_0_28])])).
% 0.19/0.49  cnf(c_0_67, negated_conjecture, (r1_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,esk2_0))|k3_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,esk2_0))!=k7_lattices(esk1_0,esk2_0)|~m1_subset_1(k7_lattices(esk1_0,X1),u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_34]), c_0_64]), c_0_17])]), c_0_20])).
% 0.19/0.49  cnf(c_0_68, plain, (k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))=k3_lattices(X1,k7_lattices(X1,X3),k7_lattices(X1,X2))|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v4_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_65, c_0_44])).
% 0.19/0.49  cnf(c_0_69, negated_conjecture, (~r1_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0))|~m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_44]), c_0_26]), c_0_17])]), c_0_20])).
% 0.19/0.49  cnf(c_0_70, negated_conjecture, (r1_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,esk2_0))|k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),k7_lattices(esk1_0,X1))!=k7_lattices(esk1_0,esk2_0)|~m1_subset_1(k7_lattices(esk1_0,X1),u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_34]), c_0_64]), c_0_17])]), c_0_20])).
% 0.19/0.49  cnf(c_0_71, negated_conjecture, (~r1_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_55])])).
% 0.19/0.49  cnf(c_0_72, negated_conjecture, (~m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_50]), c_0_26])]), c_0_71])).
% 0.19/0.49  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_44]), c_0_26]), c_0_17])]), c_0_20]), ['proof']).
% 0.19/0.49  # SZS output end CNFRefutation
% 0.19/0.49  # Proof object total steps             : 74
% 0.19/0.49  # Proof object clause steps            : 51
% 0.19/0.49  # Proof object formula steps           : 23
% 0.19/0.49  # Proof object conjectures             : 35
% 0.19/0.49  # Proof object clause conjectures      : 32
% 0.19/0.49  # Proof object formula conjectures     : 3
% 0.19/0.49  # Proof object initial clauses used    : 23
% 0.19/0.49  # Proof object initial formulas used   : 11
% 0.19/0.49  # Proof object generating inferences   : 26
% 0.19/0.49  # Proof object simplifying inferences  : 83
% 0.19/0.49  # Training examples: 0 positive, 0 negative
% 0.19/0.49  # Parsed axioms                        : 11
% 0.19/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.49  # Initial clauses                      : 28
% 0.19/0.49  # Removed in clause preprocessing      : 1
% 0.19/0.49  # Initial clauses in saturation        : 27
% 0.19/0.49  # Processed clauses                    : 971
% 0.19/0.49  # ...of these trivial                  : 31
% 0.19/0.49  # ...subsumed                          : 450
% 0.19/0.49  # ...remaining for further processing  : 490
% 0.19/0.49  # Other redundant clauses eliminated   : 0
% 0.19/0.49  # Clauses deleted for lack of memory   : 0
% 0.19/0.49  # Backward-subsumed                    : 112
% 0.19/0.49  # Backward-rewritten                   : 17
% 0.19/0.49  # Generated clauses                    : 4646
% 0.19/0.49  # ...of the previous two non-trivial   : 4267
% 0.19/0.49  # Contextual simplify-reflections      : 12
% 0.19/0.49  # Paramodulations                      : 4646
% 0.19/0.49  # Factorizations                       : 0
% 0.19/0.49  # Equation resolutions                 : 0
% 0.19/0.49  # Propositional unsat checks           : 0
% 0.19/0.49  #    Propositional check models        : 0
% 0.19/0.49  #    Propositional check unsatisfiable : 0
% 0.19/0.49  #    Propositional clauses             : 0
% 0.19/0.49  #    Propositional clauses after purity: 0
% 0.19/0.49  #    Propositional unsat core size     : 0
% 0.19/0.49  #    Propositional preprocessing time  : 0.000
% 0.19/0.49  #    Propositional encoding time       : 0.000
% 0.19/0.49  #    Propositional solver time         : 0.000
% 0.19/0.49  #    Success case prop preproc time    : 0.000
% 0.19/0.49  #    Success case prop encoding time   : 0.000
% 0.19/0.49  #    Success case prop solver time     : 0.000
% 0.19/0.49  # Current number of processed clauses  : 334
% 0.19/0.49  #    Positive orientable unit clauses  : 48
% 0.19/0.49  #    Positive unorientable unit clauses: 0
% 0.19/0.49  #    Negative unit clauses             : 8
% 0.19/0.49  #    Non-unit-clauses                  : 278
% 0.19/0.49  # Current number of unprocessed clauses: 3278
% 0.19/0.49  # ...number of literals in the above   : 13734
% 0.19/0.49  # Current number of archived formulas  : 0
% 0.19/0.49  # Current number of archived clauses   : 156
% 0.19/0.49  # Clause-clause subsumption calls (NU) : 35372
% 0.19/0.49  # Rec. Clause-clause subsumption calls : 25661
% 0.19/0.49  # Non-unit clause-clause subsumptions  : 478
% 0.19/0.49  # Unit Clause-clause subsumption calls : 982
% 0.19/0.49  # Rewrite failures with RHS unbound    : 0
% 0.19/0.49  # BW rewrite match attempts            : 61
% 0.19/0.49  # BW rewrite match successes           : 14
% 0.19/0.49  # Condensation attempts                : 0
% 0.19/0.49  # Condensation successes               : 0
% 0.19/0.49  # Termbank termtop insertions          : 173131
% 0.19/0.49  
% 0.19/0.49  # -------------------------------------------------
% 0.19/0.49  # User time                : 0.142 s
% 0.19/0.49  # System time              : 0.010 s
% 0.19/0.49  # Total time               : 0.151 s
% 0.19/0.49  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
