%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1457+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:17 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  173 (28179 expanded)
%              Number of clauses        :  146 (8852 expanded)
%              Number of leaves         :   13 (6957 expanded)
%              Depth                    :   22
%              Number of atoms          :  478 (197196 expanded)
%              Number of equality atoms :  135 (68093 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_filter_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( k7_lattices(X1,k4_filter_0(X1,X2,X3)) = k4_lattices(X1,X2,k7_lattices(X1,X3))
                & k7_lattices(X1,k7_filter_0(X1,X2,X3)) = k3_lattices(X1,k4_lattices(X1,X2,k7_lattices(X1,X3)),k4_lattices(X1,k7_lattices(X1,X2),X3))
                & k7_lattices(X1,k7_filter_0(X1,X2,X3)) = k7_filter_0(X1,X2,k7_lattices(X1,X3))
                & k7_lattices(X1,k7_filter_0(X1,X2,X3)) = k7_filter_0(X1,k7_lattices(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_filter_1)).

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

fof(dt_k7_lattices,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(t49_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k7_lattices(X1,k7_lattices(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).

fof(commutativity_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(t55_filter_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k4_filter_0(X1,X2,X3) = k3_lattices(X1,k7_lattices(X1,X2),X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_filter_0)).

fof(dt_k4_filter_0,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_filter_0(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_filter_0)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_lattices)).

fof(d11_filter_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k7_filter_0(X1,X2,X3) = k4_lattices(X1,k4_filter_0(X1,X2,X3),k4_filter_0(X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_filter_0)).

fof(t51_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k7_filter_0(X1,X2,X3) = k3_lattices(X1,k4_lattices(X1,X2,X3),k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_filter_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v17_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( k7_lattices(X1,k4_filter_0(X1,X2,X3)) = k4_lattices(X1,X2,k7_lattices(X1,X3))
                  & k7_lattices(X1,k7_filter_0(X1,X2,X3)) = k3_lattices(X1,k4_lattices(X1,X2,k7_lattices(X1,X3)),k4_lattices(X1,k7_lattices(X1,X2),X3))
                  & k7_lattices(X1,k7_filter_0(X1,X2,X3)) = k7_filter_0(X1,X2,k7_lattices(X1,X3))
                  & k7_lattices(X1,k7_filter_0(X1,X2,X3)) = k7_filter_0(X1,k7_lattices(X1,X2),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_filter_1])).

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

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v17_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & ( k7_lattices(esk1_0,k4_filter_0(esk1_0,esk2_0,esk3_0)) != k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))
      | k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) != k3_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),k4_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0))
      | k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) != k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))
      | k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) != k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ l3_lattices(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | m1_subset_1(k7_lattices(X20,X21),u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).

fof(c_0_17,plain,(
    ! [X23,X24] :
      ( v2_struct_0(X23)
      | ~ v10_lattices(X23)
      | ~ v17_lattices(X23)
      | ~ l3_lattices(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | k7_lattices(X23,k7_lattices(X23,X24)) = X24 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_lattices])])])])).

fof(c_0_18,plain,(
    ! [X5,X6,X7] :
      ( v2_struct_0(X5)
      | ~ v4_lattices(X5)
      | ~ l2_lattices(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | k3_lattices(X5,X6,X7) = k3_lattices(X5,X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).

cnf(c_0_19,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X17,X18,X19] :
      ( v2_struct_0(X17)
      | ~ v6_lattices(X17)
      | ~ l1_lattices(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | m1_subset_1(k4_lattices(X17,X18,X19),u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

cnf(c_0_24,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_25,plain,(
    ! [X34,X35,X36] :
      ( v2_struct_0(X34)
      | ~ v10_lattices(X34)
      | ~ v17_lattices(X34)
      | ~ l3_lattices(X34)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | ~ m1_subset_1(X36,u1_struct_0(X34))
      | k4_filter_0(X34,X35,X36) = k3_lattices(X34,k7_lattices(X34,X35),X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_filter_0])])])])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_29,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ v10_lattices(X14)
      | ~ l3_lattices(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | m1_subset_1(k4_filter_0(X14,X15,X16),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_filter_0])])])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | k7_lattices(X1,k7_lattices(X1,X2)) = X2
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( v4_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])]),c_0_22])).

fof(c_0_34,plain,(
    ! [X22] :
      ( ( l1_lattices(X22)
        | ~ l3_lattices(X22) )
      & ( l2_lattices(X22)
        | ~ l3_lattices(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_20]),c_0_21])]),c_0_22])).

fof(c_0_37,plain,(
    ! [X25,X26,X27] :
      ( v2_struct_0(X25)
      | ~ v10_lattices(X25)
      | ~ v17_lattices(X25)
      | ~ l3_lattices(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ m1_subset_1(X27,u1_struct_0(X25))
      | k7_lattices(X25,k4_lattices(X25,X26,X27)) = k3_lattices(X25,k7_lattices(X25,X26),k7_lattices(X25,X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_lattices])])])])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | k4_filter_0(X1,X2,X3) = k3_lattices(X1,k7_lattices(X1,X2),X3)
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_21])]),c_0_22])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk1_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_28]),c_0_21])]),c_0_22])).

fof(c_0_41,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ v10_lattices(X31)
      | ~ v17_lattices(X31)
      | ~ l3_lattices(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | ~ m1_subset_1(X33,u1_struct_0(X31))
      | k7_lattices(X31,k3_lattices(X31,X32,X33)) = k4_lattices(X31,k7_lattices(X31,X32),k7_lattices(X31,X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t51_lattices])])])])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_filter_0(X1,X2,X3),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,esk3_0)) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_28]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_44,negated_conjecture,
    ( k3_lattices(esk1_0,X1,esk3_0) = k3_lattices(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_28]),c_0_33])]),c_0_22])).

cnf(c_0_45,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk1_0,X1,esk2_0),u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_27]),c_0_36])]),c_0_22])).

cnf(c_0_47,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | k7_lattices(X1,k4_lattices(X1,X2,X3)) = k3_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,esk2_0)) = k4_filter_0(esk1_0,X1,k7_lattices(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,esk2_0)) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_27]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( k3_lattices(esk1_0,X1,esk2_0) = k3_lattices(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_33])]),c_0_22])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk1_0,X1,esk3_0),u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_28]),c_0_36])]),c_0_22])).

cnf(c_0_53,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,esk3_0)) = k4_filter_0(esk1_0,X1,k7_lattices(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_40]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | k7_lattices(X1,k3_lattices(X1,X2,X3)) = k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k4_filter_0(esk1_0,X1,k7_lattices(esk1_0,esk2_0)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_39]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_56,negated_conjecture,
    ( k4_filter_0(esk1_0,k7_lattices(esk1_0,esk3_0),X1) = k3_lattices(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_43]),c_0_31]),c_0_40]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( k3_lattices(esk1_0,X1,esk3_0) = k3_lattices(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_21])])).

cnf(c_0_58,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,X1),esk3_0) = k4_filter_0(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_28]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk1_0,X1,esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_21])])).

cnf(c_0_60,negated_conjecture,
    ( k4_filter_0(esk1_0,X1,k7_lattices(esk1_0,esk2_0)) = k7_lattices(esk1_0,k4_lattices(esk1_0,X1,esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_31]),c_0_27]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k4_filter_0(esk1_0,X1,k7_lattices(esk1_0,esk3_0)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_40]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_62,negated_conjecture,
    ( k4_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),X1) = k3_lattices(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_50]),c_0_31]),c_0_39]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_63,negated_conjecture,
    ( k3_lattices(esk1_0,X1,esk2_0) = k3_lattices(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_45]),c_0_21])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk1_0,X1,esk3_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_47]),c_0_21])])).

cnf(c_0_65,negated_conjecture,
    ( k4_filter_0(esk1_0,X1,k7_lattices(esk1_0,esk3_0)) = k7_lattices(esk1_0,k4_lattices(esk1_0,X1,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_53]),c_0_31]),c_0_28]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_66,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,X1),esk2_0) = k4_filter_0(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_27]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_67,negated_conjecture,
    ( k7_lattices(esk1_0,k3_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),X1)) = k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_43]),c_0_31]),c_0_40]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k3_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_40]),c_0_39])])).

cnf(c_0_69,negated_conjecture,
    ( k3_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,X1)) = k4_filter_0(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,k4_lattices(esk1_0,X1,esk2_0))) = k4_lattices(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_59]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_71,negated_conjecture,
    ( k7_lattices(esk1_0,k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0)) = k3_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_60]),c_0_39]),c_0_40])])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(k3_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_39]),c_0_40])])).

cnf(c_0_73,negated_conjecture,
    ( k3_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,X1)) = k4_filter_0(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(k7_lattices(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_63]),c_0_31]),c_0_27]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_74,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,k4_lattices(esk1_0,X1,esk3_0))) = k4_lattices(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_64]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_75,negated_conjecture,
    ( k7_lattices(esk1_0,k4_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0)) = k3_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_65]),c_0_40]),c_0_39])])).

cnf(c_0_76,negated_conjecture,
    ( k4_filter_0(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0) = k3_lattices(esk1_0,esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_43]),c_0_40])])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk1_0,k4_filter_0(esk1_0,X1,k7_lattices(esk1_0,esk2_0))),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_55]),c_0_21])]),c_0_22])).

cnf(c_0_78,negated_conjecture,
    ( k7_lattices(esk1_0,k4_filter_0(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0))) = k4_lattices(esk1_0,esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_49]),c_0_50]),c_0_39]),c_0_28])])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k4_filter_0(esk1_0,esk2_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_39]),c_0_27])])).

cnf(c_0_80,negated_conjecture,
    ( k7_lattices(esk1_0,k3_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0))) = k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_40])])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(k4_filter_0(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_40]),c_0_28])])).

cnf(c_0_82,negated_conjecture,
    ( k7_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))) = k4_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_39])])).

fof(c_0_83,plain,(
    ! [X8,X9,X10] :
      ( v2_struct_0(X8)
      | ~ v10_lattices(X8)
      | ~ l3_lattices(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | k7_filter_0(X8,X9,X10) = k4_lattices(X8,k4_filter_0(X8,X9,X10),k4_filter_0(X8,X10,X9)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_filter_0])])])])).

cnf(c_0_84,negated_conjecture,
    ( k3_lattices(esk1_0,esk3_0,esk2_0) = k3_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_43]),c_0_76]),c_0_28]),c_0_40])])).

cnf(c_0_85,negated_conjecture,
    ( k3_lattices(esk1_0,X1,k7_lattices(esk1_0,esk3_0)) = k3_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_40]),c_0_33])]),c_0_22])).

cnf(c_0_86,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,k4_filter_0(esk1_0,X1,k7_lattices(esk1_0,esk2_0)))) = k4_filter_0(esk1_0,X1,k7_lattices(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_55]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_28])])).

cnf(c_0_88,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,k4_filter_0(esk1_0,esk2_0,esk3_0))) = k4_filter_0(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_79]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_89,negated_conjecture,
    ( k7_lattices(esk1_0,k4_filter_0(esk1_0,esk2_0,esk3_0)) = k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_69]),c_0_39]),c_0_27])])).

cnf(c_0_90,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,k4_filter_0(esk1_0,esk3_0,esk2_0))) = k4_filter_0(esk1_0,esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_81]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_91,negated_conjecture,
    ( k7_lattices(esk1_0,k4_filter_0(esk1_0,esk3_0,esk2_0)) = k4_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_73]),c_0_40]),c_0_28])])).

cnf(c_0_92,plain,
    ( v2_struct_0(X1)
    | k7_filter_0(X1,X2,X3) = k4_lattices(X1,k4_filter_0(X1,X2,X3),k4_filter_0(X1,X3,X2))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_93,negated_conjecture,
    ( k4_filter_0(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0) = k3_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_84])).

cnf(c_0_94,negated_conjecture,
    ( k4_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) = k3_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_50]),c_0_39])])).

cnf(c_0_95,negated_conjecture,
    ( k7_lattices(esk1_0,k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),X1)) = k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_50]),c_0_31]),c_0_39]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_96,negated_conjecture,
    ( k3_lattices(esk1_0,X1,k7_lattices(esk1_0,esk3_0)) = k4_filter_0(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_85]),c_0_31]),c_0_28]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_97,negated_conjecture,
    ( k4_filter_0(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0)) = k7_lattices(esk1_0,k4_lattices(esk1_0,esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_78]),c_0_28])])).

cnf(c_0_98,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,k4_lattices(esk1_0,esk3_0,esk2_0))) = k4_lattices(esk1_0,esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_87]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_99,negated_conjecture,
    ( k4_filter_0(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0)) = k3_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_43]),c_0_40])])).

cnf(c_0_100,negated_conjecture,
    ( k3_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0)) = k4_filter_0(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89]),c_0_71])).

cnf(c_0_101,negated_conjecture,
    ( k4_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),k7_lattices(esk1_0,esk3_0)) = k3_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_50]),c_0_39])])).

cnf(c_0_102,negated_conjecture,
    ( k3_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) = k4_filter_0(esk1_0,esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91]),c_0_75])).

cnf(c_0_103,negated_conjecture,
    ( k4_lattices(esk1_0,k4_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),k3_lattices(esk1_0,esk2_0,esk3_0)) = k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_40]),c_0_27]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(k3_lattices(esk1_0,esk2_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_94]),c_0_28]),c_0_39]),c_0_20]),c_0_21])]),c_0_22])).

fof(c_0_105,plain,(
    ! [X28,X29,X30] :
      ( v2_struct_0(X28)
      | ~ v10_lattices(X28)
      | ~ v17_lattices(X28)
      | ~ l3_lattices(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | k7_filter_0(X28,X29,X30) = k3_lattices(X28,k4_lattices(X28,X29,X30),k4_lattices(X28,k7_lattices(X28,X29),k7_lattices(X28,X30))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t51_filter_1])])])])).

cnf(c_0_106,negated_conjecture,
    ( k4_lattices(esk1_0,esk3_0,esk2_0) = k4_lattices(esk1_0,esk2_0,esk3_0)
    | ~ l2_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97]),c_0_98]),c_0_43]),c_0_40]),c_0_39])])).

cnf(c_0_107,negated_conjecture,
    ( k4_filter_0(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0)) = k4_filter_0(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_108,negated_conjecture,
    ( k4_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),k7_lattices(esk1_0,esk3_0)) = k4_filter_0(esk1_0,esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ m1_subset_1(k4_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_103]),c_0_104]),c_0_36])]),c_0_22])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk1_0,k4_filter_0(esk1_0,X1,k7_lattices(esk1_0,esk3_0))),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_61]),c_0_21])]),c_0_22])).

cnf(c_0_111,negated_conjecture,
    ( k7_lattices(esk1_0,k4_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))) = k4_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_53]),c_0_43]),c_0_40]),c_0_27])])).

cnf(c_0_112,plain,
    ( v2_struct_0(X1)
    | k7_filter_0(X1,X2,X3) = k3_lattices(X1,k4_lattices(X1,X2,X3),k4_lattices(X1,k7_lattices(X1,X2),k7_lattices(X1,X3)))
    | ~ v10_lattices(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_113,negated_conjecture,
    ( k4_lattices(esk1_0,esk3_0,esk2_0) = k4_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_45]),c_0_21])])).

cnf(c_0_114,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,k4_filter_0(esk1_0,X1,k7_lattices(esk1_0,esk3_0)))) = k4_filter_0(esk1_0,X1,k7_lattices(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_61]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_115,negated_conjecture,
    ( k4_lattices(esk1_0,k4_filter_0(esk1_0,esk3_0,esk2_0),k4_filter_0(esk1_0,esk2_0,esk3_0)) = k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),k7_lattices(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_107]),c_0_108]),c_0_40]),c_0_39]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_116,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,esk3_0)) = k7_lattices(esk1_0,k3_lattices(esk1_0,X1,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_28]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_117,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,esk2_0)) = k7_lattices(esk1_0,k3_lattices(esk1_0,X1,esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_27]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_118,negated_conjecture,
    ( m1_subset_1(k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_47]),c_0_21])])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk1_0,esk2_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_27])])).

cnf(c_0_120,negated_conjecture,
    ( k3_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0),k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0))) = k7_filter_0(esk1_0,esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_31]),c_0_27]),c_0_28]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_121,negated_conjecture,
    ( k4_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) = k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_111]),c_0_27])])).

cnf(c_0_122,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk1_0,k7_lattices(esk1_0,k4_filter_0(esk1_0,X1,k7_lattices(esk1_0,esk3_0)))),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_110]),c_0_21])]),c_0_22])).

cnf(c_0_123,negated_conjecture,
    ( k4_lattices(esk1_0,k4_filter_0(esk1_0,esk2_0,esk3_0),k4_filter_0(esk1_0,esk3_0,esk2_0)) = k7_filter_0(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_107]),c_0_108]),c_0_39]),c_0_40]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_124,negated_conjecture,
    ( k3_lattices(esk1_0,k4_lattices(esk1_0,X1,k7_lattices(esk1_0,esk3_0)),k4_lattices(esk1_0,k7_lattices(esk1_0,X1),esk3_0)) = k7_filter_0(esk1_0,X1,k7_lattices(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_40]),c_0_43]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_125,negated_conjecture,
    ( k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),k7_lattices(esk1_0,esk3_0)) = k7_filter_0(esk1_0,esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_115]),c_0_27]),c_0_28]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_126,negated_conjecture,
    ( k7_lattices(esk1_0,k4_filter_0(esk1_0,esk2_0,esk3_0)) != k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))
    | k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) != k3_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),k4_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0))
    | k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) != k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))
    | k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) != k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_127,negated_conjecture,
    ( k7_lattices(esk1_0,k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0)) = k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_50]),c_0_39])])).

cnf(c_0_128,negated_conjecture,
    ( k7_lattices(esk1_0,k3_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0)) = k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_43]),c_0_40])])).

cnf(c_0_129,negated_conjecture,
    ( m1_subset_1(k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_61]),c_0_27])])).

cnf(c_0_130,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,X1),k7_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0))) = k7_lattices(esk1_0,k4_lattices(esk1_0,X1,k3_lattices(esk1_0,esk2_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_104]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_131,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0))) = k4_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_119]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_132,negated_conjecture,
    ( k3_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0),k7_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0))) = k7_filter_0(esk1_0,esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_117]),c_0_84]),c_0_28])])).

cnf(c_0_133,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0)),k3_lattices(esk1_0,esk2_0,esk3_0)) = k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_103,c_0_121])).

cnf(c_0_134,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_111]),c_0_27])])).

cnf(c_0_135,negated_conjecture,
    ( m1_subset_1(k4_filter_0(esk1_0,X1,esk3_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_28]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_136,negated_conjecture,
    ( k3_lattices(esk1_0,k4_lattices(esk1_0,X1,k7_lattices(esk1_0,esk2_0)),k4_lattices(esk1_0,k7_lattices(esk1_0,X1),esk2_0)) = k7_filter_0(esk1_0,X1,k7_lattices(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_39]),c_0_50]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_137,negated_conjecture,
    ( k7_filter_0(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0)) = k7_filter_0(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_123]),c_0_28]),c_0_27]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_138,negated_conjecture,
    ( k3_lattices(esk1_0,k4_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),k7_lattices(esk1_0,esk3_0)),k4_lattices(esk1_0,esk2_0,esk3_0)) = k7_filter_0(esk1_0,esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_50]),c_0_125]),c_0_39])])).

cnf(c_0_139,negated_conjecture,
    ( k3_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),k4_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0)) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0))
    | k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0))
    | k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0) != k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))
    | k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_126,c_0_89])).

cnf(c_0_140,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0) = k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_57]),c_0_100]),c_0_89]),c_0_39])])).

cnf(c_0_141,negated_conjecture,
    ( k4_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) = k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_63]),c_0_102]),c_0_91]),c_0_40])])).

cnf(c_0_142,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)))) = k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_129]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_143,negated_conjecture,
    ( k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))) = k7_filter_0(esk1_0,esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_132]),c_0_133]),c_0_134])])).

cnf(c_0_144,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk1_0,k4_filter_0(esk1_0,X1,esk3_0)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_135]),c_0_21])]),c_0_22])).

cnf(c_0_145,negated_conjecture,
    ( k3_lattices(esk1_0,k4_lattices(esk1_0,k7_lattices(esk1_0,esk3_0),k7_lattices(esk1_0,esk2_0)),k4_lattices(esk1_0,esk2_0,esk3_0)) = k7_filter_0(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_43]),c_0_113]),c_0_137]),c_0_40])])).

cnf(c_0_146,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0)),k4_lattices(esk1_0,esk2_0,esk3_0)) = k7_filter_0(esk1_0,esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_116]),c_0_27])])).

cnf(c_0_147,negated_conjecture,
    ( k4_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0),k4_filter_0(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0))) = k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_94]),c_0_28]),c_0_39]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_148,negated_conjecture,
    ( k4_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0),k4_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0))) = k7_filter_0(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_27]),c_0_40]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_149,negated_conjecture,
    ( m1_subset_1(k3_lattices(esk1_0,esk2_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_62]),c_0_39]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_150,negated_conjecture,
    ( k3_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0))) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0))
    | k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0))
    | k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_140])]),c_0_141])).

cnf(c_0_151,negated_conjecture,
    ( k7_filter_0(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)) = k7_lattices(esk1_0,k7_filter_0(esk1_0,esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_142,c_0_143])).

cnf(c_0_152,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0))) = k3_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_104]),c_0_31]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_153,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_94]),c_0_39])])).

cnf(c_0_154,negated_conjecture,
    ( k7_filter_0(esk1_0,esk3_0,esk2_0) = k7_filter_0(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_117]),c_0_84]),c_0_146]),c_0_28])])).

cnf(c_0_155,negated_conjecture,
    ( k4_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0),k7_lattices(esk1_0,k4_lattices(esk1_0,esk3_0,esk2_0))) = k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_147,c_0_97])).

cnf(c_0_156,negated_conjecture,
    ( k4_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0),k7_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0))) = k7_filter_0(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_148,c_0_121])).

cnf(c_0_157,negated_conjecture,
    ( m1_subset_1(k3_lattices(esk1_0,X1,esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_149,c_0_63])).

cnf(c_0_158,negated_conjecture,
    ( k3_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0))) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0))
    | k7_lattices(esk1_0,k7_filter_0(esk1_0,esk3_0,esk2_0)) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0))
    | k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_150,c_0_151])).

cnf(c_0_159,negated_conjecture,
    ( k7_lattices(esk1_0,k3_lattices(esk1_0,k7_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0)),X1)) = k4_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0),k7_lattices(esk1_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_152]),c_0_31]),c_0_153]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_160,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,k3_lattices(esk1_0,esk2_0,esk3_0)),k4_lattices(esk1_0,esk2_0,esk3_0)) = k7_filter_0(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_146,c_0_154])).

cnf(c_0_161,negated_conjecture,
    ( k7_filter_0(esk1_0,k7_lattices(esk1_0,esk3_0),esk2_0) = k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_155,c_0_113]),c_0_156])).

cnf(c_0_162,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk1_0,X1,k7_lattices(esk1_0,esk3_0)),u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_40]),c_0_36])]),c_0_22])).

cnf(c_0_163,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk1_0,k3_lattices(esk1_0,X1,esk2_0)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_157]),c_0_21])]),c_0_22])).

cnf(c_0_164,negated_conjecture,
    ( k3_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0))) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0))
    | k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_158,c_0_154])])).

cnf(c_0_165,negated_conjecture,
    ( k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),esk3_0) = k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_160]),c_0_156]),c_0_161]),c_0_119])])).

cnf(c_0_166,negated_conjecture,
    ( k3_lattices(esk1_0,k4_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),X1),k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,X1))) = k7_filter_0(esk1_0,k7_lattices(esk1_0,esk2_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_50]),c_0_31]),c_0_39]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_167,negated_conjecture,
    ( k3_lattices(esk1_0,X1,k4_lattices(esk1_0,X2,k7_lattices(esk1_0,esk3_0))) = k3_lattices(esk1_0,k4_lattices(esk1_0,X2,k7_lattices(esk1_0,esk3_0)),X1)
    | ~ l1_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ l2_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_162]),c_0_33])]),c_0_22])).

cnf(c_0_168,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_128]),c_0_40])])).

cnf(c_0_169,negated_conjecture,
    ( k3_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk3_0)),k4_lattices(esk1_0,esk3_0,k7_lattices(esk1_0,esk2_0))) != k7_lattices(esk1_0,k7_filter_0(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_164,c_0_165])])).

cnf(c_0_170,negated_conjecture,
    ( ~ l1_lattices(esk1_0)
    | ~ l2_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_167]),c_0_141]),c_0_165]),c_0_28]),c_0_141]),c_0_168]),c_0_27])]),c_0_169])).

cnf(c_0_171,negated_conjecture,
    ( ~ l2_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_47]),c_0_21])])).

cnf(c_0_172,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_45]),c_0_21])]),
    [proof]).

%------------------------------------------------------------------------------
