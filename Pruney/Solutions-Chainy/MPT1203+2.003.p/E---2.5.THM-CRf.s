%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:23 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 931 expanded)
%              Number of clauses        :   56 ( 309 expanded)
%              Number of leaves         :   10 ( 231 expanded)
%              Depth                    :   13
%              Number of atoms          :  311 (6747 expanded)
%              Number of equality atoms :   55 (1544 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(commutativity_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

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

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X25,X26,X27,X28] :
      ( v2_struct_0(X25)
      | ~ v10_lattices(X25)
      | ~ v11_lattices(X25)
      | ~ l3_lattices(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ m1_subset_1(X27,u1_struct_0(X25))
      | ~ m1_subset_1(X28,u1_struct_0(X25))
      | k3_lattices(X25,X26,k4_lattices(X25,X27,X28)) = k4_lattices(X25,k3_lattices(X25,X26,X27),k3_lattices(X25,X26,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_lattices])])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v11_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    & k4_lattices(esk1_0,esk2_0,esk3_0) = k4_lattices(esk1_0,esk2_0,esk4_0)
    & k3_lattices(esk1_0,esk2_0,esk3_0) = k3_lattices(esk1_0,esk2_0,esk4_0)
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X18] :
      ( ( l1_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( l2_lattices(X18)
        | ~ l3_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_14,plain,(
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

fof(c_0_15,plain,(
    ! [X19,X20,X21] :
      ( v2_struct_0(X19)
      | ~ v4_lattices(X19)
      | ~ l2_lattices(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | k3_lattices(X19,X20,X21) = k1_lattices(X19,X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

fof(c_0_16,plain,(
    ! [X6,X7,X8] :
      ( v2_struct_0(X6)
      | ~ v4_lattices(X6)
      | ~ l2_lattices(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | k3_lattices(X6,X7,X8) = k3_lattices(X6,X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,k4_lattices(X1,X3,X4)) = k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X2,X4))
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v11_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_26,plain,(
    ! [X12,X13,X14] :
      ( ( ~ r1_lattices(X12,X13,X14)
        | k1_lattices(X12,X13,X14) = X14
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l2_lattices(X12) )
      & ( k1_lattices(X12,X13,X14) != X14
        | r1_lattices(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l2_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

cnf(c_0_27,negated_conjecture,
    ( k4_lattices(esk1_0,k3_lattices(esk1_0,X1,X2),k3_lattices(esk1_0,X1,X3)) = k3_lattices(esk1_0,X1,k4_lattices(esk1_0,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( l2_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v4_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( k3_lattices(esk1_0,esk2_0,esk3_0) = k3_lattices(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,plain,
    ( k3_lattices(X1,X2,X3) = k1_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X22,X23,X24] :
      ( v2_struct_0(X22)
      | ~ v6_lattices(X22)
      | ~ v8_lattices(X22)
      | ~ l3_lattices(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | ~ m1_subset_1(X24,u1_struct_0(X22))
      | r1_lattices(X22,k4_lattices(X22,X23,X24),X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_lattices])])])])).

cnf(c_0_36,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( k4_lattices(esk1_0,k3_lattices(esk1_0,X1,X2),k1_lattices(esk1_0,X1,X3)) = k3_lattices(esk1_0,X1,k4_lattices(esk1_0,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_28]),c_0_29])]),c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( k1_lattices(esk1_0,esk4_0,esk2_0) = k3_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_28]),c_0_29])]),c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( k1_lattices(esk1_0,X1,esk4_0) = esk4_0
    | ~ r1_lattices(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_21]),c_0_28])])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,k4_lattices(X1,X2,X3),X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_19]),c_0_20])]),c_0_21])).

fof(c_0_44,plain,(
    ! [X15,X16,X17] :
      ( v2_struct_0(X15)
      | ~ v6_lattices(X15)
      | ~ l1_lattices(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | m1_subset_1(k4_lattices(X15,X16,X17),u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

cnf(c_0_45,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,negated_conjecture,
    ( k4_lattices(esk1_0,k3_lattices(esk1_0,esk4_0,X1),k3_lattices(esk1_0,esk2_0,esk3_0)) = k3_lattices(esk1_0,esk4_0,k4_lattices(esk1_0,X1,esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_32]),c_0_33])])).

cnf(c_0_47,negated_conjecture,
    ( k1_lattices(esk1_0,k4_lattices(esk1_0,esk4_0,X1),esk4_0) = esk4_0
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_33]),c_0_42]),c_0_43]),c_0_20])]),c_0_21])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( l1_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_20])).

fof(c_0_50,plain,(
    ! [X9,X10,X11] :
      ( v2_struct_0(X9)
      | ~ v6_lattices(X9)
      | ~ l1_lattices(X9)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | k4_lattices(X9,X10,X11) = k4_lattices(X9,X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_51,negated_conjecture,
    ( k4_lattices(esk1_0,k3_lattices(esk1_0,X1,X2),k3_lattices(esk1_0,X3,X1)) = k3_lattices(esk1_0,X1,k4_lattices(esk1_0,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_28]),c_0_29])]),c_0_21])).

cnf(c_0_52,negated_conjecture,
    ( k4_lattices(esk1_0,k3_lattices(esk1_0,X1,esk4_0),k3_lattices(esk1_0,esk2_0,esk3_0)) = k3_lattices(esk1_0,esk4_0,k4_lattices(esk1_0,X1,esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_25]),c_0_33]),c_0_28]),c_0_29])]),c_0_21])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_54,negated_conjecture,
    ( k1_lattices(esk1_0,k4_lattices(esk1_0,esk4_0,X1),esk4_0) = esk4_0
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_33]),c_0_43])]),c_0_21])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k3_lattices(esk1_0,esk3_0,k4_lattices(esk1_0,esk4_0,esk2_0)) = k3_lattices(esk1_0,esk4_0,k4_lattices(esk1_0,esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_32]),c_0_33]),c_0_53])])).

cnf(c_0_57,negated_conjecture,
    ( k4_lattices(esk1_0,esk2_0,esk3_0) = k4_lattices(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_58,plain,
    ( k1_lattices(X1,X2,X3) = k1_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_31])).

cnf(c_0_59,negated_conjecture,
    ( k1_lattices(esk1_0,k4_lattices(esk1_0,X1,esk4_0),esk4_0) = esk4_0
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_49]),c_0_33]),c_0_43])]),c_0_21])).

cnf(c_0_60,negated_conjecture,
    ( k1_lattices(esk1_0,X1,esk3_0) = esk3_0
    | ~ r1_lattices(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_53]),c_0_21]),c_0_28])])).

cnf(c_0_61,negated_conjecture,
    ( k3_lattices(esk1_0,esk4_0,k4_lattices(esk1_0,esk3_0,esk2_0)) = k3_lattices(esk1_0,esk3_0,k4_lattices(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_55]),c_0_57]),c_0_49]),c_0_32]),c_0_33]),c_0_43])]),c_0_21])).

cnf(c_0_62,negated_conjecture,
    ( k1_lattices(esk1_0,esk4_0,X1) = k1_lattices(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_33]),c_0_28]),c_0_29])]),c_0_21])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk1_0,esk2_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_57]),c_0_33]),c_0_32])]),c_0_21]),c_0_49]),c_0_43])])).

cnf(c_0_64,negated_conjecture,
    ( k1_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0),esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_57]),c_0_32])])).

cnf(c_0_65,negated_conjecture,
    ( k1_lattices(esk1_0,k4_lattices(esk1_0,esk3_0,X1),esk3_0) = esk3_0
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_41]),c_0_53]),c_0_42]),c_0_43]),c_0_20])]),c_0_21])).

cnf(c_0_66,negated_conjecture,
    ( k3_lattices(esk1_0,esk4_0,k4_lattices(esk1_0,esk2_0,esk3_0)) = k3_lattices(esk1_0,esk3_0,k4_lattices(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_55]),c_0_49]),c_0_32]),c_0_53]),c_0_43])]),c_0_21])).

cnf(c_0_67,negated_conjecture,
    ( k1_lattices(esk1_0,esk4_0,k4_lattices(esk1_0,esk2_0,esk3_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( k1_lattices(esk1_0,k4_lattices(esk1_0,esk3_0,X1),esk3_0) = esk3_0
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_48]),c_0_49]),c_0_53]),c_0_43])]),c_0_21])).

cnf(c_0_69,negated_conjecture,
    ( k1_lattices(esk1_0,esk3_0,X1) = k1_lattices(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_53]),c_0_28]),c_0_29])]),c_0_21])).

cnf(c_0_70,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_71,negated_conjecture,
    ( esk4_0 = k3_lattices(esk1_0,esk3_0,k4_lattices(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_66]),c_0_67]),c_0_63]),c_0_33]),c_0_28]),c_0_29])]),c_0_21])).

cnf(c_0_72,negated_conjecture,
    ( k1_lattices(esk1_0,k4_lattices(esk1_0,X1,esk3_0),esk3_0) = esk3_0
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_55]),c_0_49]),c_0_53]),c_0_43])]),c_0_21])).

cnf(c_0_73,negated_conjecture,
    ( k1_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0),esk3_0) = k1_lattices(esk1_0,esk3_0,k4_lattices(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( k3_lattices(esk1_0,esk3_0,k4_lattices(esk1_0,esk2_0,esk3_0)) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( k1_lattices(esk1_0,esk3_0,k4_lattices(esk1_0,esk2_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_32])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_24]),c_0_75]),c_0_63]),c_0_53]),c_0_28]),c_0_29])]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:49:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.50  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.18/0.50  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.50  #
% 0.18/0.50  # Preprocessing time       : 0.028 s
% 0.18/0.50  # Presaturation interreduction done
% 0.18/0.50  
% 0.18/0.50  # Proof found!
% 0.18/0.50  # SZS status Theorem
% 0.18/0.50  # SZS output start CNFRefutation
% 0.18/0.50  fof(t32_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((k4_lattices(X1,X2,X3)=k4_lattices(X1,X2,X4)&k3_lattices(X1,X2,X3)=k3_lattices(X1,X2,X4))=>X3=X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_lattices)).
% 0.18/0.50  fof(t31_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>k3_lattices(X1,X2,k4_lattices(X1,X3,X4))=k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_lattices)).
% 0.18/0.50  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.18/0.50  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.18/0.50  fof(redefinition_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 0.18/0.50  fof(commutativity_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 0.18/0.50  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 0.18/0.50  fof(t23_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>r1_lattices(X1,k4_lattices(X1,X2,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_lattices)).
% 0.18/0.50  fof(dt_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_lattices)).
% 0.18/0.50  fof(commutativity_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 0.18/0.50  fof(c_0_10, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((k4_lattices(X1,X2,X3)=k4_lattices(X1,X2,X4)&k3_lattices(X1,X2,X3)=k3_lattices(X1,X2,X4))=>X3=X4)))))), inference(assume_negation,[status(cth)],[t32_lattices])).
% 0.18/0.50  fof(c_0_11, plain, ![X25, X26, X27, X28]:(v2_struct_0(X25)|~v10_lattices(X25)|~v11_lattices(X25)|~l3_lattices(X25)|(~m1_subset_1(X26,u1_struct_0(X25))|(~m1_subset_1(X27,u1_struct_0(X25))|(~m1_subset_1(X28,u1_struct_0(X25))|k3_lattices(X25,X26,k4_lattices(X25,X27,X28))=k4_lattices(X25,k3_lattices(X25,X26,X27),k3_lattices(X25,X26,X28)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_lattices])])])])).
% 0.18/0.50  fof(c_0_12, negated_conjecture, ((((~v2_struct_0(esk1_0)&v10_lattices(esk1_0))&v11_lattices(esk1_0))&l3_lattices(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(m1_subset_1(esk3_0,u1_struct_0(esk1_0))&(m1_subset_1(esk4_0,u1_struct_0(esk1_0))&((k4_lattices(esk1_0,esk2_0,esk3_0)=k4_lattices(esk1_0,esk2_0,esk4_0)&k3_lattices(esk1_0,esk2_0,esk3_0)=k3_lattices(esk1_0,esk2_0,esk4_0))&esk3_0!=esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.18/0.50  fof(c_0_13, plain, ![X18]:((l1_lattices(X18)|~l3_lattices(X18))&(l2_lattices(X18)|~l3_lattices(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.18/0.50  fof(c_0_14, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.18/0.50  fof(c_0_15, plain, ![X19, X20, X21]:(v2_struct_0(X19)|~v4_lattices(X19)|~l2_lattices(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|k3_lattices(X19,X20,X21)=k1_lattices(X19,X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).
% 0.18/0.50  fof(c_0_16, plain, ![X6, X7, X8]:(v2_struct_0(X6)|~v4_lattices(X6)|~l2_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))|k3_lattices(X6,X7,X8)=k3_lattices(X6,X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).
% 0.18/0.50  cnf(c_0_17, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,k4_lattices(X1,X3,X4))=k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X2,X4))|~v10_lattices(X1)|~v11_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.50  cnf(c_0_18, negated_conjecture, (v11_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.50  cnf(c_0_19, negated_conjecture, (v10_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.50  cnf(c_0_20, negated_conjecture, (l3_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.50  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.50  cnf(c_0_22, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.50  cnf(c_0_23, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.50  cnf(c_0_24, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.50  cnf(c_0_25, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.50  fof(c_0_26, plain, ![X12, X13, X14]:((~r1_lattices(X12,X13,X14)|k1_lattices(X12,X13,X14)=X14|~m1_subset_1(X14,u1_struct_0(X12))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~l2_lattices(X12)))&(k1_lattices(X12,X13,X14)!=X14|r1_lattices(X12,X13,X14)|~m1_subset_1(X14,u1_struct_0(X12))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~l2_lattices(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.18/0.50  cnf(c_0_27, negated_conjecture, (k4_lattices(esk1_0,k3_lattices(esk1_0,X1,X2),k3_lattices(esk1_0,X1,X3))=k3_lattices(esk1_0,X1,k4_lattices(esk1_0,X2,X3))|~m1_subset_1(X3,u1_struct_0(esk1_0))|~m1_subset_1(X2,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.18/0.50  cnf(c_0_28, negated_conjecture, (l2_lattices(esk1_0)), inference(spm,[status(thm)],[c_0_22, c_0_20])).
% 0.18/0.50  cnf(c_0_29, negated_conjecture, (v4_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_19]), c_0_20])]), c_0_21])).
% 0.18/0.50  cnf(c_0_30, negated_conjecture, (k3_lattices(esk1_0,esk2_0,esk3_0)=k3_lattices(esk1_0,esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.50  cnf(c_0_31, plain, (k3_lattices(X1,X2,X3)=k1_lattices(X1,X3,X2)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l2_lattices(X1)|~v4_lattices(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.50  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.50  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.50  cnf(c_0_34, plain, (k1_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.50  fof(c_0_35, plain, ![X22, X23, X24]:(v2_struct_0(X22)|~v6_lattices(X22)|~v8_lattices(X22)|~l3_lattices(X22)|(~m1_subset_1(X23,u1_struct_0(X22))|(~m1_subset_1(X24,u1_struct_0(X22))|r1_lattices(X22,k4_lattices(X22,X23,X24),X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_lattices])])])])).
% 0.18/0.50  cnf(c_0_36, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.50  cnf(c_0_37, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.50  cnf(c_0_38, negated_conjecture, (k4_lattices(esk1_0,k3_lattices(esk1_0,X1,X2),k1_lattices(esk1_0,X1,X3))=k3_lattices(esk1_0,X1,k4_lattices(esk1_0,X2,X3))|~m1_subset_1(X3,u1_struct_0(esk1_0))|~m1_subset_1(X2,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_24]), c_0_28]), c_0_29])]), c_0_21])).
% 0.18/0.50  cnf(c_0_39, negated_conjecture, (k1_lattices(esk1_0,esk4_0,esk2_0)=k3_lattices(esk1_0,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_28]), c_0_29])]), c_0_21])).
% 0.18/0.50  cnf(c_0_40, negated_conjecture, (k1_lattices(esk1_0,X1,esk4_0)=esk4_0|~r1_lattices(esk1_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_21]), c_0_28])])).
% 0.18/0.50  cnf(c_0_41, plain, (v2_struct_0(X1)|r1_lattices(X1,k4_lattices(X1,X2,X3),X2)|~v6_lattices(X1)|~v8_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.50  cnf(c_0_42, negated_conjecture, (v8_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_19]), c_0_20])]), c_0_21])).
% 0.18/0.50  cnf(c_0_43, negated_conjecture, (v6_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_19]), c_0_20])]), c_0_21])).
% 0.18/0.50  fof(c_0_44, plain, ![X15, X16, X17]:(v2_struct_0(X15)|~v6_lattices(X15)|~l1_lattices(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|m1_subset_1(k4_lattices(X15,X16,X17),u1_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).
% 0.18/0.50  cnf(c_0_45, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.50  cnf(c_0_46, negated_conjecture, (k4_lattices(esk1_0,k3_lattices(esk1_0,esk4_0,X1),k3_lattices(esk1_0,esk2_0,esk3_0))=k3_lattices(esk1_0,esk4_0,k4_lattices(esk1_0,X1,esk2_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_32]), c_0_33])])).
% 0.18/0.50  cnf(c_0_47, negated_conjecture, (k1_lattices(esk1_0,k4_lattices(esk1_0,esk4_0,X1),esk4_0)=esk4_0|~m1_subset_1(k4_lattices(esk1_0,esk4_0,X1),u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_33]), c_0_42]), c_0_43]), c_0_20])]), c_0_21])).
% 0.18/0.50  cnf(c_0_48, plain, (v2_struct_0(X1)|m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.50  cnf(c_0_49, negated_conjecture, (l1_lattices(esk1_0)), inference(spm,[status(thm)],[c_0_45, c_0_20])).
% 0.18/0.50  fof(c_0_50, plain, ![X9, X10, X11]:(v2_struct_0(X9)|~v6_lattices(X9)|~l1_lattices(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))|k4_lattices(X9,X10,X11)=k4_lattices(X9,X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).
% 0.18/0.50  cnf(c_0_51, negated_conjecture, (k4_lattices(esk1_0,k3_lattices(esk1_0,X1,X2),k3_lattices(esk1_0,X3,X1))=k3_lattices(esk1_0,X1,k4_lattices(esk1_0,X2,X3))|~m1_subset_1(X3,u1_struct_0(esk1_0))|~m1_subset_1(X2,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_25]), c_0_28]), c_0_29])]), c_0_21])).
% 0.18/0.50  cnf(c_0_52, negated_conjecture, (k4_lattices(esk1_0,k3_lattices(esk1_0,X1,esk4_0),k3_lattices(esk1_0,esk2_0,esk3_0))=k3_lattices(esk1_0,esk4_0,k4_lattices(esk1_0,X1,esk2_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_25]), c_0_33]), c_0_28]), c_0_29])]), c_0_21])).
% 0.18/0.50  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.50  cnf(c_0_54, negated_conjecture, (k1_lattices(esk1_0,k4_lattices(esk1_0,esk4_0,X1),esk4_0)=esk4_0|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_33]), c_0_43])]), c_0_21])).
% 0.18/0.50  cnf(c_0_55, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.18/0.50  cnf(c_0_56, negated_conjecture, (k3_lattices(esk1_0,esk3_0,k4_lattices(esk1_0,esk4_0,esk2_0))=k3_lattices(esk1_0,esk4_0,k4_lattices(esk1_0,esk3_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_32]), c_0_33]), c_0_53])])).
% 0.18/0.50  cnf(c_0_57, negated_conjecture, (k4_lattices(esk1_0,esk2_0,esk3_0)=k4_lattices(esk1_0,esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.50  cnf(c_0_58, plain, (k1_lattices(X1,X2,X3)=k1_lattices(X1,X3,X2)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l2_lattices(X1)|~v4_lattices(X1)), inference(spm,[status(thm)],[c_0_24, c_0_31])).
% 0.18/0.50  cnf(c_0_59, negated_conjecture, (k1_lattices(esk1_0,k4_lattices(esk1_0,X1,esk4_0),esk4_0)=esk4_0|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_49]), c_0_33]), c_0_43])]), c_0_21])).
% 0.18/0.50  cnf(c_0_60, negated_conjecture, (k1_lattices(esk1_0,X1,esk3_0)=esk3_0|~r1_lattices(esk1_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_53]), c_0_21]), c_0_28])])).
% 0.18/0.50  cnf(c_0_61, negated_conjecture, (k3_lattices(esk1_0,esk4_0,k4_lattices(esk1_0,esk3_0,esk2_0))=k3_lattices(esk1_0,esk3_0,k4_lattices(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_55]), c_0_57]), c_0_49]), c_0_32]), c_0_33]), c_0_43])]), c_0_21])).
% 0.18/0.50  cnf(c_0_62, negated_conjecture, (k1_lattices(esk1_0,esk4_0,X1)=k1_lattices(esk1_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_33]), c_0_28]), c_0_29])]), c_0_21])).
% 0.18/0.50  cnf(c_0_63, negated_conjecture, (m1_subset_1(k4_lattices(esk1_0,esk2_0,esk3_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_57]), c_0_33]), c_0_32])]), c_0_21]), c_0_49]), c_0_43])])).
% 0.18/0.50  cnf(c_0_64, negated_conjecture, (k1_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0),esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_57]), c_0_32])])).
% 0.18/0.50  cnf(c_0_65, negated_conjecture, (k1_lattices(esk1_0,k4_lattices(esk1_0,esk3_0,X1),esk3_0)=esk3_0|~m1_subset_1(k4_lattices(esk1_0,esk3_0,X1),u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_41]), c_0_53]), c_0_42]), c_0_43]), c_0_20])]), c_0_21])).
% 0.18/0.50  cnf(c_0_66, negated_conjecture, (k3_lattices(esk1_0,esk4_0,k4_lattices(esk1_0,esk2_0,esk3_0))=k3_lattices(esk1_0,esk3_0,k4_lattices(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_55]), c_0_49]), c_0_32]), c_0_53]), c_0_43])]), c_0_21])).
% 0.18/0.50  cnf(c_0_67, negated_conjecture, (k1_lattices(esk1_0,esk4_0,k4_lattices(esk1_0,esk2_0,esk3_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.18/0.50  cnf(c_0_68, negated_conjecture, (k1_lattices(esk1_0,k4_lattices(esk1_0,esk3_0,X1),esk3_0)=esk3_0|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_48]), c_0_49]), c_0_53]), c_0_43])]), c_0_21])).
% 0.18/0.50  cnf(c_0_69, negated_conjecture, (k1_lattices(esk1_0,esk3_0,X1)=k1_lattices(esk1_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_53]), c_0_28]), c_0_29])]), c_0_21])).
% 0.18/0.50  cnf(c_0_70, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.50  cnf(c_0_71, negated_conjecture, (esk4_0=k3_lattices(esk1_0,esk3_0,k4_lattices(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_66]), c_0_67]), c_0_63]), c_0_33]), c_0_28]), c_0_29])]), c_0_21])).
% 0.18/0.50  cnf(c_0_72, negated_conjecture, (k1_lattices(esk1_0,k4_lattices(esk1_0,X1,esk3_0),esk3_0)=esk3_0|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_55]), c_0_49]), c_0_53]), c_0_43])]), c_0_21])).
% 0.18/0.50  cnf(c_0_73, negated_conjecture, (k1_lattices(esk1_0,k4_lattices(esk1_0,esk2_0,esk3_0),esk3_0)=k1_lattices(esk1_0,esk3_0,k4_lattices(esk1_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_69, c_0_63])).
% 0.18/0.50  cnf(c_0_74, negated_conjecture, (k3_lattices(esk1_0,esk3_0,k4_lattices(esk1_0,esk2_0,esk3_0))!=esk3_0), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 0.18/0.50  cnf(c_0_75, negated_conjecture, (k1_lattices(esk1_0,esk3_0,k4_lattices(esk1_0,esk2_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_32])])).
% 0.18/0.50  cnf(c_0_76, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_24]), c_0_75]), c_0_63]), c_0_53]), c_0_28]), c_0_29])]), c_0_21]), ['proof']).
% 0.18/0.50  # SZS output end CNFRefutation
% 0.18/0.50  # Proof object total steps             : 77
% 0.18/0.50  # Proof object clause steps            : 56
% 0.18/0.50  # Proof object formula steps           : 21
% 0.18/0.50  # Proof object conjectures             : 45
% 0.18/0.50  # Proof object clause conjectures      : 42
% 0.18/0.50  # Proof object formula conjectures     : 3
% 0.18/0.50  # Proof object initial clauses used    : 22
% 0.18/0.50  # Proof object initial formulas used   : 10
% 0.18/0.50  # Proof object generating inferences   : 33
% 0.18/0.50  # Proof object simplifying inferences  : 125
% 0.18/0.50  # Training examples: 0 positive, 0 negative
% 0.18/0.50  # Parsed axioms                        : 10
% 0.18/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.50  # Initial clauses                      : 27
% 0.18/0.50  # Removed in clause preprocessing      : 1
% 0.18/0.50  # Initial clauses in saturation        : 26
% 0.18/0.50  # Processed clauses                    : 784
% 0.18/0.50  # ...of these trivial                  : 44
% 0.18/0.50  # ...subsumed                          : 346
% 0.18/0.50  # ...remaining for further processing  : 394
% 0.18/0.50  # Other redundant clauses eliminated   : 0
% 0.18/0.50  # Clauses deleted for lack of memory   : 0
% 0.18/0.50  # Backward-subsumed                    : 5
% 0.18/0.50  # Backward-rewritten                   : 168
% 0.18/0.50  # Generated clauses                    : 6970
% 0.18/0.50  # ...of the previous two non-trivial   : 6513
% 0.18/0.50  # Contextual simplify-reflections      : 7
% 0.18/0.50  # Paramodulations                      : 6970
% 0.18/0.50  # Factorizations                       : 0
% 0.18/0.50  # Equation resolutions                 : 0
% 0.18/0.50  # Propositional unsat checks           : 0
% 0.18/0.50  #    Propositional check models        : 0
% 0.18/0.50  #    Propositional check unsatisfiable : 0
% 0.18/0.50  #    Propositional clauses             : 0
% 0.18/0.50  #    Propositional clauses after purity: 0
% 0.18/0.50  #    Propositional unsat core size     : 0
% 0.18/0.50  #    Propositional preprocessing time  : 0.000
% 0.18/0.50  #    Propositional encoding time       : 0.000
% 0.18/0.50  #    Propositional solver time         : 0.000
% 0.18/0.50  #    Success case prop preproc time    : 0.000
% 0.18/0.50  #    Success case prop encoding time   : 0.000
% 0.18/0.50  #    Success case prop solver time     : 0.000
% 0.18/0.50  # Current number of processed clauses  : 195
% 0.18/0.50  #    Positive orientable unit clauses  : 64
% 0.18/0.50  #    Positive unorientable unit clauses: 0
% 0.18/0.50  #    Negative unit clauses             : 2
% 0.18/0.50  #    Non-unit-clauses                  : 129
% 0.18/0.50  # Current number of unprocessed clauses: 5742
% 0.18/0.50  # ...number of literals in the above   : 24172
% 0.18/0.50  # Current number of archived formulas  : 0
% 0.18/0.50  # Current number of archived clauses   : 199
% 0.18/0.50  # Clause-clause subsumption calls (NU) : 5692
% 0.18/0.50  # Rec. Clause-clause subsumption calls : 4450
% 0.18/0.50  # Non-unit clause-clause subsumptions  : 358
% 0.18/0.50  # Unit Clause-clause subsumption calls : 170
% 0.18/0.50  # Rewrite failures with RHS unbound    : 0
% 0.18/0.50  # BW rewrite match attempts            : 1069
% 0.18/0.50  # BW rewrite match successes           : 27
% 0.18/0.50  # Condensation attempts                : 0
% 0.18/0.50  # Condensation successes               : 0
% 0.18/0.50  # Termbank termtop insertions          : 268208
% 0.18/0.50  
% 0.18/0.50  # -------------------------------------------------
% 0.18/0.50  # User time                : 0.159 s
% 0.18/0.50  # System time              : 0.010 s
% 0.18/0.50  # Total time               : 0.169 s
% 0.18/0.50  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
