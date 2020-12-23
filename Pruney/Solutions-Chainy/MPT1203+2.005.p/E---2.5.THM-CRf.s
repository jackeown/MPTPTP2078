%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:24 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 674 expanded)
%              Number of clauses        :   53 ( 219 expanded)
%              Number of leaves         :    9 ( 166 expanded)
%              Depth                    :   14
%              Number of atoms          :  302 (5075 expanded)
%              Number of equality atoms :   52 (1190 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_lattices,conjecture,(
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
                 => ( ( k4_lattices(X1,X2,X3) = k4_lattices(X1,X2,X4)
                      & k3_lattices(X1,X2,X3) = k3_lattices(X1,X2,X4) )
                   => X3 = X4 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_lattices)).

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

fof(commutativity_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

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

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
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
                   => ( ( k4_lattices(X1,X2,X3) = k4_lattices(X1,X2,X4)
                        & k3_lattices(X1,X2,X3) = k3_lattices(X1,X2,X4) )
                     => X3 = X4 ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_lattices])).

fof(c_0_10,plain,(
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

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v10_lattices(esk3_0)
    & v11_lattices(esk3_0)
    & l3_lattices(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & k4_lattices(esk3_0,esk4_0,esk5_0) = k4_lattices(esk3_0,esk4_0,esk6_0)
    & k3_lattices(esk3_0,esk4_0,esk5_0) = k3_lattices(esk3_0,esk4_0,esk6_0)
    & esk5_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X6,X7,X8] :
      ( v2_struct_0(X6)
      | ~ v4_lattices(X6)
      | ~ l2_lattices(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | k3_lattices(X6,X7,X8) = k3_lattices(X6,X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).

cnf(c_0_13,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v10_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l3_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X21,X22,X23] :
      ( v2_struct_0(X21)
      | ~ v6_lattices(X21)
      | ~ l1_lattices(X21)
      | ~ m1_subset_1(X22,u1_struct_0(X21))
      | ~ m1_subset_1(X23,u1_struct_0(X21))
      | k4_lattices(X21,X22,X23) = k2_lattices(X21,X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

cnf(c_0_18,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_19,plain,(
    ! [X24,X25,X26,X27] :
      ( v2_struct_0(X24)
      | ~ v10_lattices(X24)
      | ~ v11_lattices(X24)
      | ~ l3_lattices(X24)
      | ~ m1_subset_1(X25,u1_struct_0(X24))
      | ~ m1_subset_1(X26,u1_struct_0(X24))
      | ~ m1_subset_1(X27,u1_struct_0(X24))
      | k3_lattices(X24,X25,k4_lattices(X24,X26,X27)) = k4_lattices(X24,k3_lattices(X24,X25,X26),k3_lattices(X24,X25,X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_lattices])])])])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( v4_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])]),c_0_16])).

fof(c_0_23,plain,(
    ! [X17] :
      ( ( l1_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( l2_lattices(X17)
        | ~ l3_lattices(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_24,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v8_lattices(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | k1_lattices(X9,k2_lattices(X9,X10,X11),X11) = X11
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk1_1(X9),u1_struct_0(X9))
        | v8_lattices(X9)
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk2_1(X9),u1_struct_0(X9))
        | v8_lattices(X9)
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( k1_lattices(X9,k2_lattices(X9,esk1_1(X9),esk2_1(X9)),esk2_1(X9)) != esk2_1(X9)
        | v8_lattices(X9)
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( v6_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_28,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,k4_lattices(X1,X3,X4)) = k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X2,X4))
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( v11_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( k3_lattices(esk3_0,X1,esk4_0) = k3_lattices(esk3_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])]),c_0_16])).

cnf(c_0_32,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ v6_lattices(X14)
      | ~ l1_lattices(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | m1_subset_1(k4_lattices(X14,X15,X16),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

cnf(c_0_34,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( k2_lattices(esk3_0,X1,esk6_0) = k4_lattices(esk3_0,X1,esk6_0)
    | ~ l1_lattices(esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])]),c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( v8_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( k4_lattices(esk3_0,k3_lattices(esk3_0,X1,X2),k3_lattices(esk3_0,X1,esk6_0)) = k3_lattices(esk3_0,X1,k4_lattices(esk3_0,X2,esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_26]),c_0_30]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( k3_lattices(esk3_0,X1,esk4_0) = k3_lattices(esk3_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_15])])).

cnf(c_0_39,negated_conjecture,
    ( k4_lattices(esk3_0,esk4_0,esk5_0) = k4_lattices(esk3_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( k3_lattices(esk3_0,X1,esk6_0) = k3_lattices(esk3_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_26]),c_0_22])]),c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_43,plain,(
    ! [X18,X19,X20] :
      ( v2_struct_0(X18)
      | ~ v4_lattices(X18)
      | ~ l2_lattices(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | k3_lattices(X18,X19,X20) = k1_lattices(X18,X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

cnf(c_0_44,negated_conjecture,
    ( k1_lattices(esk3_0,k4_lattices(esk3_0,X1,esk6_0),esk6_0) = esk6_0
    | ~ l1_lattices(esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_26]),c_0_36]),c_0_15])]),c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( k4_lattices(esk3_0,k3_lattices(esk3_0,esk4_0,X1),k3_lattices(esk3_0,X1,esk6_0)) = k3_lattices(esk3_0,X1,k4_lattices(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_21])])).

cnf(c_0_46,negated_conjecture,
    ( k3_lattices(esk3_0,X1,esk6_0) = k3_lattices(esk3_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_32]),c_0_15])])).

cnf(c_0_47,negated_conjecture,
    ( k3_lattices(esk3_0,X1,esk5_0) = k3_lattices(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_41]),c_0_22])]),c_0_16])).

cnf(c_0_48,negated_conjecture,
    ( k2_lattices(esk3_0,X1,esk5_0) = k4_lattices(esk3_0,X1,esk5_0)
    | ~ l1_lattices(esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_41]),c_0_27])]),c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))
    | ~ l1_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_39]),c_0_26]),c_0_21]),c_0_27])]),c_0_16])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( k1_lattices(esk3_0,k4_lattices(esk3_0,esk4_0,esk5_0),esk6_0) = esk6_0
    | ~ l1_lattices(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_39]),c_0_21])])).

cnf(c_0_52,negated_conjecture,
    ( k4_lattices(esk3_0,k3_lattices(esk3_0,X1,X2),k3_lattices(esk3_0,X1,esk5_0)) = k3_lattices(esk3_0,X1,k4_lattices(esk3_0,X2,esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_41]),c_0_30]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( k4_lattices(esk3_0,k3_lattices(esk3_0,esk4_0,X1),k3_lattices(esk3_0,esk6_0,X1)) = k3_lattices(esk3_0,X1,k4_lattices(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( k3_lattices(esk3_0,X1,esk5_0) = k3_lattices(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_32]),c_0_15])])).

cnf(c_0_55,negated_conjecture,
    ( k1_lattices(esk3_0,k4_lattices(esk3_0,X1,esk5_0),esk5_0) = esk5_0
    | ~ l1_lattices(esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_48]),c_0_41]),c_0_36]),c_0_15])]),c_0_16])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk3_0,X1,esk5_0),u1_struct_0(esk3_0))
    | ~ l1_lattices(esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_41]),c_0_27])]),c_0_16])).

cnf(c_0_57,negated_conjecture,
    ( k3_lattices(esk3_0,X1,k4_lattices(esk3_0,esk4_0,esk5_0)) = k3_lattices(esk3_0,k4_lattices(esk3_0,esk4_0,esk5_0),X1)
    | ~ l1_lattices(esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_49]),c_0_22])]),c_0_16])).

cnf(c_0_58,negated_conjecture,
    ( k3_lattices(esk3_0,k4_lattices(esk3_0,esk4_0,esk5_0),esk6_0) = esk6_0
    | ~ l1_lattices(esk3_0)
    | ~ l2_lattices(esk3_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_26]),c_0_22])]),c_0_16]),c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( k4_lattices(esk3_0,k3_lattices(esk3_0,esk6_0,X1),k3_lattices(esk3_0,esk5_0,esk6_0)) = k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,X1,esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_46]),c_0_26]),c_0_41])])).

cnf(c_0_60,negated_conjecture,
    ( k3_lattices(esk3_0,esk4_0,esk5_0) = k3_lattices(esk3_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_61,negated_conjecture,
    ( k4_lattices(esk3_0,k3_lattices(esk3_0,esk4_0,esk5_0),k3_lattices(esk3_0,esk5_0,esk6_0)) = k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_41]),c_0_26])])).

cnf(c_0_62,negated_conjecture,
    ( k3_lattices(esk3_0,k4_lattices(esk3_0,X1,esk5_0),esk5_0) = esk5_0
    | ~ l1_lattices(esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l2_lattices(esk3_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_55]),c_0_41]),c_0_22])]),c_0_16]),c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,esk4_0,esk5_0)) = esk6_0
    | ~ l1_lattices(esk3_0)
    | ~ l2_lattices(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_26])])).

cnf(c_0_64,negated_conjecture,
    ( k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,esk4_0,esk5_0)) = k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_38]),c_0_60]),c_0_61]),c_0_21]),c_0_26])])).

cnf(c_0_65,negated_conjecture,
    ( k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0)) = esk5_0
    | ~ l1_lattices(esk3_0)
    | ~ l2_lattices(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_62]),c_0_41]),c_0_21])])).

cnf(c_0_66,negated_conjecture,
    ( k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0)) = esk6_0
    | ~ l1_lattices(esk3_0)
    | ~ l2_lattices(esk3_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_68,negated_conjecture,
    ( ~ l1_lattices(esk3_0)
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_69,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_70,negated_conjecture,
    ( ~ l2_lattices(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_15])])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_32]),c_0_15])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:57:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.20/0.43  # and selection function PSelectComplexExceptRRHorn.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.029 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t32_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((k4_lattices(X1,X2,X3)=k4_lattices(X1,X2,X4)&k3_lattices(X1,X2,X3)=k3_lattices(X1,X2,X4))=>X3=X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_lattices)).
% 0.20/0.43  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.20/0.43  fof(commutativity_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 0.20/0.43  fof(redefinition_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 0.20/0.43  fof(t31_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>k3_lattices(X1,X2,k4_lattices(X1,X3,X4))=k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_lattices)).
% 0.20/0.43  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.20/0.43  fof(d8_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v8_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 0.20/0.43  fof(dt_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_lattices)).
% 0.20/0.43  fof(redefinition_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 0.20/0.43  fof(c_0_9, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((k4_lattices(X1,X2,X3)=k4_lattices(X1,X2,X4)&k3_lattices(X1,X2,X3)=k3_lattices(X1,X2,X4))=>X3=X4)))))), inference(assume_negation,[status(cth)],[t32_lattices])).
% 0.20/0.43  fof(c_0_10, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.20/0.43  fof(c_0_11, negated_conjecture, ((((~v2_struct_0(esk3_0)&v10_lattices(esk3_0))&v11_lattices(esk3_0))&l3_lattices(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&((k4_lattices(esk3_0,esk4_0,esk5_0)=k4_lattices(esk3_0,esk4_0,esk6_0)&k3_lattices(esk3_0,esk4_0,esk5_0)=k3_lattices(esk3_0,esk4_0,esk6_0))&esk5_0!=esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.20/0.43  fof(c_0_12, plain, ![X6, X7, X8]:(v2_struct_0(X6)|~v4_lattices(X6)|~l2_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))|k3_lattices(X6,X7,X8)=k3_lattices(X6,X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).
% 0.20/0.43  cnf(c_0_13, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_14, negated_conjecture, (v10_lattices(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_15, negated_conjecture, (l3_lattices(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  fof(c_0_17, plain, ![X21, X22, X23]:(v2_struct_0(X21)|~v6_lattices(X21)|~l1_lattices(X21)|~m1_subset_1(X22,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|k4_lattices(X21,X22,X23)=k2_lattices(X21,X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).
% 0.20/0.43  cnf(c_0_18, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  fof(c_0_19, plain, ![X24, X25, X26, X27]:(v2_struct_0(X24)|~v10_lattices(X24)|~v11_lattices(X24)|~l3_lattices(X24)|(~m1_subset_1(X25,u1_struct_0(X24))|(~m1_subset_1(X26,u1_struct_0(X24))|(~m1_subset_1(X27,u1_struct_0(X24))|k3_lattices(X24,X25,k4_lattices(X24,X26,X27))=k4_lattices(X24,k3_lattices(X24,X25,X26),k3_lattices(X24,X25,X27)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_lattices])])])])).
% 0.20/0.43  cnf(c_0_20, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_22, negated_conjecture, (v4_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])]), c_0_16])).
% 0.20/0.43  fof(c_0_23, plain, ![X17]:((l1_lattices(X17)|~l3_lattices(X17))&(l2_lattices(X17)|~l3_lattices(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.20/0.43  fof(c_0_24, plain, ![X9, X10, X11]:((~v8_lattices(X9)|(~m1_subset_1(X10,u1_struct_0(X9))|(~m1_subset_1(X11,u1_struct_0(X9))|k1_lattices(X9,k2_lattices(X9,X10,X11),X11)=X11))|(v2_struct_0(X9)|~l3_lattices(X9)))&((m1_subset_1(esk1_1(X9),u1_struct_0(X9))|v8_lattices(X9)|(v2_struct_0(X9)|~l3_lattices(X9)))&((m1_subset_1(esk2_1(X9),u1_struct_0(X9))|v8_lattices(X9)|(v2_struct_0(X9)|~l3_lattices(X9)))&(k1_lattices(X9,k2_lattices(X9,esk1_1(X9),esk2_1(X9)),esk2_1(X9))!=esk2_1(X9)|v8_lattices(X9)|(v2_struct_0(X9)|~l3_lattices(X9)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).
% 0.20/0.43  cnf(c_0_25, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_27, negated_conjecture, (v6_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_14]), c_0_15])]), c_0_16])).
% 0.20/0.43  cnf(c_0_28, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_29, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,k4_lattices(X1,X3,X4))=k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X2,X4))|~v10_lattices(X1)|~v11_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_30, negated_conjecture, (v11_lattices(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_31, negated_conjecture, (k3_lattices(esk3_0,X1,esk4_0)=k3_lattices(esk3_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])]), c_0_16])).
% 0.20/0.43  cnf(c_0_32, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  fof(c_0_33, plain, ![X14, X15, X16]:(v2_struct_0(X14)|~v6_lattices(X14)|~l1_lattices(X14)|~m1_subset_1(X15,u1_struct_0(X14))|~m1_subset_1(X16,u1_struct_0(X14))|m1_subset_1(k4_lattices(X14,X15,X16),u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).
% 0.20/0.43  cnf(c_0_34, plain, (k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3|v2_struct_0(X1)|~v8_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.43  cnf(c_0_35, negated_conjecture, (k2_lattices(esk3_0,X1,esk6_0)=k4_lattices(esk3_0,X1,esk6_0)|~l1_lattices(esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])]), c_0_16])).
% 0.20/0.43  cnf(c_0_36, negated_conjecture, (v8_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_14]), c_0_15])]), c_0_16])).
% 0.20/0.43  cnf(c_0_37, negated_conjecture, (k4_lattices(esk3_0,k3_lattices(esk3_0,X1,X2),k3_lattices(esk3_0,X1,esk6_0))=k3_lattices(esk3_0,X1,k4_lattices(esk3_0,X2,esk6_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_26]), c_0_30]), c_0_14]), c_0_15])]), c_0_16])).
% 0.20/0.43  cnf(c_0_38, negated_conjecture, (k3_lattices(esk3_0,X1,esk4_0)=k3_lattices(esk3_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_15])])).
% 0.20/0.43  cnf(c_0_39, negated_conjecture, (k4_lattices(esk3_0,esk4_0,esk5_0)=k4_lattices(esk3_0,esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_40, negated_conjecture, (k3_lattices(esk3_0,X1,esk6_0)=k3_lattices(esk3_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_26]), c_0_22])]), c_0_16])).
% 0.20/0.43  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_42, plain, (v2_struct_0(X1)|m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.43  fof(c_0_43, plain, ![X18, X19, X20]:(v2_struct_0(X18)|~v4_lattices(X18)|~l2_lattices(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|k3_lattices(X18,X19,X20)=k1_lattices(X18,X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).
% 0.20/0.43  cnf(c_0_44, negated_conjecture, (k1_lattices(esk3_0,k4_lattices(esk3_0,X1,esk6_0),esk6_0)=esk6_0|~l1_lattices(esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_26]), c_0_36]), c_0_15])]), c_0_16])).
% 0.20/0.43  cnf(c_0_45, negated_conjecture, (k4_lattices(esk3_0,k3_lattices(esk3_0,esk4_0,X1),k3_lattices(esk3_0,X1,esk6_0))=k3_lattices(esk3_0,X1,k4_lattices(esk3_0,esk4_0,esk5_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_21])])).
% 0.20/0.43  cnf(c_0_46, negated_conjecture, (k3_lattices(esk3_0,X1,esk6_0)=k3_lattices(esk3_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_32]), c_0_15])])).
% 0.20/0.43  cnf(c_0_47, negated_conjecture, (k3_lattices(esk3_0,X1,esk5_0)=k3_lattices(esk3_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_41]), c_0_22])]), c_0_16])).
% 0.20/0.43  cnf(c_0_48, negated_conjecture, (k2_lattices(esk3_0,X1,esk5_0)=k4_lattices(esk3_0,X1,esk5_0)|~l1_lattices(esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_41]), c_0_27])]), c_0_16])).
% 0.20/0.43  cnf(c_0_49, negated_conjecture, (m1_subset_1(k4_lattices(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))|~l1_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_39]), c_0_26]), c_0_21]), c_0_27])]), c_0_16])).
% 0.20/0.43  cnf(c_0_50, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.43  cnf(c_0_51, negated_conjecture, (k1_lattices(esk3_0,k4_lattices(esk3_0,esk4_0,esk5_0),esk6_0)=esk6_0|~l1_lattices(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_39]), c_0_21])])).
% 0.20/0.43  cnf(c_0_52, negated_conjecture, (k4_lattices(esk3_0,k3_lattices(esk3_0,X1,X2),k3_lattices(esk3_0,X1,esk5_0))=k3_lattices(esk3_0,X1,k4_lattices(esk3_0,X2,esk5_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_41]), c_0_30]), c_0_14]), c_0_15])]), c_0_16])).
% 0.20/0.43  cnf(c_0_53, negated_conjecture, (k4_lattices(esk3_0,k3_lattices(esk3_0,esk4_0,X1),k3_lattices(esk3_0,esk6_0,X1))=k3_lattices(esk3_0,X1,k4_lattices(esk3_0,esk4_0,esk5_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.43  cnf(c_0_54, negated_conjecture, (k3_lattices(esk3_0,X1,esk5_0)=k3_lattices(esk3_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_32]), c_0_15])])).
% 0.20/0.43  cnf(c_0_55, negated_conjecture, (k1_lattices(esk3_0,k4_lattices(esk3_0,X1,esk5_0),esk5_0)=esk5_0|~l1_lattices(esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_48]), c_0_41]), c_0_36]), c_0_15])]), c_0_16])).
% 0.20/0.43  cnf(c_0_56, negated_conjecture, (m1_subset_1(k4_lattices(esk3_0,X1,esk5_0),u1_struct_0(esk3_0))|~l1_lattices(esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_41]), c_0_27])]), c_0_16])).
% 0.20/0.43  cnf(c_0_57, negated_conjecture, (k3_lattices(esk3_0,X1,k4_lattices(esk3_0,esk4_0,esk5_0))=k3_lattices(esk3_0,k4_lattices(esk3_0,esk4_0,esk5_0),X1)|~l1_lattices(esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_49]), c_0_22])]), c_0_16])).
% 0.20/0.43  cnf(c_0_58, negated_conjecture, (k3_lattices(esk3_0,k4_lattices(esk3_0,esk4_0,esk5_0),esk6_0)=esk6_0|~l1_lattices(esk3_0)|~l2_lattices(esk3_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_26]), c_0_22])]), c_0_16]), c_0_49])).
% 0.20/0.43  cnf(c_0_59, negated_conjecture, (k4_lattices(esk3_0,k3_lattices(esk3_0,esk6_0,X1),k3_lattices(esk3_0,esk5_0,esk6_0))=k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,X1,esk5_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_46]), c_0_26]), c_0_41])])).
% 0.20/0.43  cnf(c_0_60, negated_conjecture, (k3_lattices(esk3_0,esk4_0,esk5_0)=k3_lattices(esk3_0,esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_61, negated_conjecture, (k4_lattices(esk3_0,k3_lattices(esk3_0,esk4_0,esk5_0),k3_lattices(esk3_0,esk5_0,esk6_0))=k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_41]), c_0_26])])).
% 0.20/0.43  cnf(c_0_62, negated_conjecture, (k3_lattices(esk3_0,k4_lattices(esk3_0,X1,esk5_0),esk5_0)=esk5_0|~l1_lattices(esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~l2_lattices(esk3_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_55]), c_0_41]), c_0_22])]), c_0_16]), c_0_56])).
% 0.20/0.43  cnf(c_0_63, negated_conjecture, (k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,esk4_0,esk5_0))=esk6_0|~l1_lattices(esk3_0)|~l2_lattices(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_26])])).
% 0.20/0.43  cnf(c_0_64, negated_conjecture, (k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,esk4_0,esk5_0))=k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_38]), c_0_60]), c_0_61]), c_0_21]), c_0_26])])).
% 0.20/0.43  cnf(c_0_65, negated_conjecture, (k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0))=esk5_0|~l1_lattices(esk3_0)|~l2_lattices(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_62]), c_0_41]), c_0_21])])).
% 0.20/0.43  cnf(c_0_66, negated_conjecture, (k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0))=esk6_0|~l1_lattices(esk3_0)|~l2_lattices(esk3_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.43  cnf(c_0_67, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_68, negated_conjecture, (~l1_lattices(esk3_0)|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 0.20/0.43  cnf(c_0_69, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  cnf(c_0_70, negated_conjecture, (~l2_lattices(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_15])])).
% 0.20/0.43  cnf(c_0_71, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_32]), c_0_15])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 72
% 0.20/0.43  # Proof object clause steps            : 53
% 0.20/0.43  # Proof object formula steps           : 19
% 0.20/0.43  # Proof object conjectures             : 45
% 0.20/0.43  # Proof object clause conjectures      : 42
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 21
% 0.20/0.43  # Proof object initial formulas used   : 9
% 0.20/0.43  # Proof object generating inferences   : 32
% 0.20/0.43  # Proof object simplifying inferences  : 97
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 9
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 28
% 0.20/0.43  # Removed in clause preprocessing      : 1
% 0.20/0.43  # Initial clauses in saturation        : 27
% 0.20/0.43  # Processed clauses                    : 363
% 0.20/0.43  # ...of these trivial                  : 1
% 0.20/0.43  # ...subsumed                          : 103
% 0.20/0.43  # ...remaining for further processing  : 259
% 0.20/0.43  # Other redundant clauses eliminated   : 0
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 32
% 0.20/0.43  # Backward-rewritten                   : 6
% 0.20/0.43  # Generated clauses                    : 1629
% 0.20/0.43  # ...of the previous two non-trivial   : 1467
% 0.20/0.43  # Contextual simplify-reflections      : 7
% 0.20/0.43  # Paramodulations                      : 1629
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 0
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 194
% 0.20/0.43  #    Positive orientable unit clauses  : 36
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 3
% 0.20/0.43  #    Non-unit-clauses                  : 155
% 0.20/0.43  # Current number of unprocessed clauses: 1155
% 0.20/0.43  # ...number of literals in the above   : 5288
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 65
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 4577
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 3352
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 142
% 0.20/0.43  # Unit Clause-clause subsumption calls : 233
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 187
% 0.20/0.43  # BW rewrite match successes           : 3
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 72570
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.083 s
% 0.20/0.43  # System time              : 0.007 s
% 0.20/0.43  # Total time               : 0.090 s
% 0.20/0.43  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
