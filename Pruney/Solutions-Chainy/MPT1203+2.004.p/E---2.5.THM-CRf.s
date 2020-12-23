%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:24 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  108 (1842 expanded)
%              Number of clauses        :   85 ( 592 expanded)
%              Number of leaves         :   11 ( 457 expanded)
%              Depth                    :   16
%              Number of atoms          :  386 (13970 expanded)
%              Number of equality atoms :   86 (3242 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   28 (   2 average)
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

fof(d9_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v9_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

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

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(dt_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k3_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_lattices)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
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

fof(c_0_13,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X27,X28] :
      ( v2_struct_0(X27)
      | ~ v6_lattices(X27)
      | ~ v8_lattices(X27)
      | ~ v9_lattices(X27)
      | ~ l3_lattices(X27)
      | ~ m1_subset_1(X28,u1_struct_0(X27))
      | k1_lattices(X27,X28,X28) = X28 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_lattices])])])])).

cnf(c_0_15,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v10_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( l3_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X21,X22,X23] :
      ( v2_struct_0(X21)
      | ~ v4_lattices(X21)
      | ~ l2_lattices(X21)
      | ~ m1_subset_1(X22,u1_struct_0(X21))
      | ~ m1_subset_1(X23,u1_struct_0(X21))
      | k3_lattices(X21,X22,X23) = k1_lattices(X21,X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

cnf(c_0_22,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_23,plain,(
    ! [X6,X7,X8] :
      ( v2_struct_0(X6)
      | ~ v4_lattices(X6)
      | ~ l2_lattices(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | k3_lattices(X6,X7,X8) = k3_lattices(X6,X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).

fof(c_0_24,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v9_lattices(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | k2_lattices(X12,X13,k1_lattices(X12,X13,X14)) = X13
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk1_1(X12),u1_struct_0(X12))
        | v9_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk2_1(X12),u1_struct_0(X12))
        | v9_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( k2_lattices(X12,esk1_1(X12),k1_lattices(X12,esk1_1(X12),esk2_1(X12))) != esk1_1(X12)
        | v9_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | k1_lattices(X1,X2,X2) = X2
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( v9_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( v8_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( v6_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( v4_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X20] :
      ( ( l1_lattices(X20)
        | ~ l3_lattices(X20) )
      & ( l2_lattices(X20)
        | ~ l3_lattices(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_34,plain,(
    ! [X24,X25,X26] :
      ( v2_struct_0(X24)
      | ~ v6_lattices(X24)
      | ~ l1_lattices(X24)
      | ~ m1_subset_1(X25,u1_struct_0(X24))
      | ~ m1_subset_1(X26,u1_struct_0(X24))
      | k4_lattices(X24,X25,X26) = k2_lattices(X24,X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

cnf(c_0_35,plain,
    ( k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( k1_lattices(esk3_0,esk6_0,esk6_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_17])]),c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( k1_lattices(esk3_0,X1,esk6_0) = k3_lattices(esk3_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_31])]),c_0_18])).

fof(c_0_40,plain,(
    ! [X29,X30,X31,X32] :
      ( v2_struct_0(X29)
      | ~ v10_lattices(X29)
      | ~ v11_lattices(X29)
      | ~ l3_lattices(X29)
      | ~ m1_subset_1(X30,u1_struct_0(X29))
      | ~ m1_subset_1(X31,u1_struct_0(X29))
      | ~ m1_subset_1(X32,u1_struct_0(X29))
      | k3_lattices(X29,X30,k4_lattices(X29,X31,X32)) = k4_lattices(X29,k3_lattices(X29,X30,X31),k3_lattices(X29,X30,X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_lattices])])])])).

cnf(c_0_41,negated_conjecture,
    ( k3_lattices(esk3_0,X1,esk6_0) = k3_lattices(esk3_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_26]),c_0_31])]),c_0_18])).

cnf(c_0_42,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( k2_lattices(esk3_0,esk6_0,esk6_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_26]),c_0_27]),c_0_17])]),c_0_18])).

fof(c_0_45,plain,(
    ! [X9,X10,X11] :
      ( v2_struct_0(X9)
      | ~ v6_lattices(X9)
      | ~ l1_lattices(X9)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | k4_lattices(X9,X10,X11) = k4_lattices(X9,X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_46,negated_conjecture,
    ( k1_lattices(esk3_0,esk4_0,esk4_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_37]),c_0_27]),c_0_28]),c_0_29]),c_0_17])]),c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( k1_lattices(esk3_0,esk5_0,esk5_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_38]),c_0_27]),c_0_28]),c_0_29]),c_0_17])]),c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( k1_lattices(esk3_0,X1,esk5_0) = k3_lattices(esk3_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_38]),c_0_31])]),c_0_18])).

fof(c_0_49,plain,(
    ! [X17,X18,X19] :
      ( v2_struct_0(X17)
      | ~ v4_lattices(X17)
      | ~ l2_lattices(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | m1_subset_1(k3_lattices(X17,X18,X19),u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_lattices])])])).

cnf(c_0_50,negated_conjecture,
    ( k3_lattices(esk3_0,esk6_0,esk6_0) = esk6_0
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_39]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_17])]),c_0_18])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,k4_lattices(X1,X3,X4)) = k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X2,X4))
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( k3_lattices(esk3_0,X1,esk6_0) = k3_lattices(esk3_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_17])])).

cnf(c_0_53,negated_conjecture,
    ( v11_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_54,negated_conjecture,
    ( k4_lattices(esk3_0,esk6_0,esk6_0) = esk6_0
    | ~ l1_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_26]),c_0_29])]),c_0_18])).

cnf(c_0_55,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( k2_lattices(esk3_0,esk4_0,esk4_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_46]),c_0_37]),c_0_27]),c_0_17])]),c_0_18])).

cnf(c_0_58,negated_conjecture,
    ( k2_lattices(esk3_0,esk5_0,esk5_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_47]),c_0_38]),c_0_27]),c_0_17])]),c_0_18])).

cnf(c_0_59,negated_conjecture,
    ( k3_lattices(esk3_0,esk5_0,esk5_0) = esk5_0
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_48]),c_0_38]),c_0_27]),c_0_28]),c_0_29]),c_0_17])]),c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( k1_lattices(esk3_0,X1,esk4_0) = k3_lattices(esk3_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_37]),c_0_31])]),c_0_18])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,negated_conjecture,
    ( k3_lattices(esk3_0,esk4_0,esk5_0) = k3_lattices(esk3_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_63,negated_conjecture,
    ( k3_lattices(esk3_0,esk6_0,esk6_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_42]),c_0_17])])).

cnf(c_0_64,negated_conjecture,
    ( k3_lattices(esk3_0,X1,esk4_0) = k3_lattices(esk3_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_37]),c_0_31])]),c_0_18])).

cnf(c_0_65,negated_conjecture,
    ( k4_lattices(esk3_0,k3_lattices(esk3_0,X1,X2),k3_lattices(esk3_0,esk6_0,X1)) = k3_lattices(esk3_0,X1,k4_lattices(esk3_0,X2,esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_26]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_66,negated_conjecture,
    ( k4_lattices(esk3_0,k3_lattices(esk3_0,X1,esk6_0),k3_lattices(esk3_0,esk6_0,X2)) = k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_26]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_67,negated_conjecture,
    ( k4_lattices(esk3_0,esk6_0,esk6_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_17])])).

cnf(c_0_68,negated_conjecture,
    ( k4_lattices(esk3_0,X1,esk4_0) = k4_lattices(esk3_0,esk4_0,X1)
    | ~ l1_lattices(esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_37]),c_0_29])]),c_0_18])).

cnf(c_0_69,negated_conjecture,
    ( k4_lattices(esk3_0,esk4_0,esk4_0) = esk4_0
    | ~ l1_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_57]),c_0_37]),c_0_29])]),c_0_18])).

cnf(c_0_70,negated_conjecture,
    ( k4_lattices(esk3_0,X1,esk5_0) = k4_lattices(esk3_0,esk5_0,X1)
    | ~ l1_lattices(esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_38]),c_0_29])]),c_0_18])).

cnf(c_0_71,negated_conjecture,
    ( k4_lattices(esk3_0,esk5_0,esk5_0) = esk5_0
    | ~ l1_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_58]),c_0_38]),c_0_29])]),c_0_18])).

cnf(c_0_72,negated_conjecture,
    ( k3_lattices(esk3_0,X1,esk5_0) = k3_lattices(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_38]),c_0_31])]),c_0_18])).

cnf(c_0_73,negated_conjecture,
    ( k3_lattices(esk3_0,esk5_0,esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_42]),c_0_17])])).

cnf(c_0_74,negated_conjecture,
    ( k2_lattices(esk3_0,X1,k3_lattices(esk3_0,X1,esk4_0)) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_60]),c_0_37]),c_0_27]),c_0_17])]),c_0_18])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k3_lattices(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_26]),c_0_37]),c_0_31])]),c_0_18])).

cnf(c_0_76,negated_conjecture,
    ( k4_lattices(esk3_0,k3_lattices(esk3_0,esk6_0,X1),esk6_0) = k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,X1,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_63]),c_0_53]),c_0_26]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_77,negated_conjecture,
    ( k3_lattices(esk3_0,X1,esk4_0) = k3_lattices(esk3_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_42]),c_0_17])])).

cnf(c_0_78,negated_conjecture,
    ( k4_lattices(esk3_0,esk4_0,esk5_0) = k4_lattices(esk3_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_79,negated_conjecture,
    ( k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,X1,X1)) = k3_lattices(esk3_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_26])])).

cnf(c_0_80,negated_conjecture,
    ( k4_lattices(esk3_0,X1,esk4_0) = k4_lattices(esk3_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_55]),c_0_17])])).

cnf(c_0_81,negated_conjecture,
    ( k4_lattices(esk3_0,esk4_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_55]),c_0_17])])).

cnf(c_0_82,negated_conjecture,
    ( k4_lattices(esk3_0,X1,esk5_0) = k4_lattices(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_55]),c_0_17])])).

cnf(c_0_83,negated_conjecture,
    ( k4_lattices(esk3_0,esk5_0,esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_55]),c_0_17])])).

cnf(c_0_84,negated_conjecture,
    ( k3_lattices(esk3_0,X1,esk5_0) = k3_lattices(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_42]),c_0_17])])).

cnf(c_0_85,negated_conjecture,
    ( k4_lattices(esk3_0,k3_lattices(esk3_0,esk5_0,X1),esk5_0) = k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,X1,esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_73]),c_0_53]),c_0_38]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_86,negated_conjecture,
    ( k2_lattices(esk3_0,esk6_0,k3_lattices(esk3_0,esk4_0,esk5_0)) = esk6_0
    | ~ l2_lattices(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_52]),c_0_62]),c_0_26]),c_0_37])])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(k3_lattices(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_42]),c_0_17])])).

cnf(c_0_88,negated_conjecture,
    ( k4_lattices(esk3_0,k3_lattices(esk3_0,esk4_0,esk5_0),esk6_0) = k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_62]),c_0_78]),c_0_37]),c_0_26])])).

cnf(c_0_89,negated_conjecture,
    ( k4_lattices(esk3_0,k3_lattices(esk3_0,X1,X2),k3_lattices(esk3_0,X1,esk5_0)) = k3_lattices(esk3_0,X1,k4_lattices(esk3_0,X2,esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_38]),c_0_53]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_90,negated_conjecture,
    ( k3_lattices(esk3_0,esk6_0,esk4_0) = k3_lattices(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_62]),c_0_37])])).

cnf(c_0_91,negated_conjecture,
    ( k3_lattices(esk3_0,esk6_0,esk5_0) = k3_lattices(esk3_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_82]),c_0_83]),c_0_38])])).

cnf(c_0_92,negated_conjecture,
    ( k2_lattices(esk3_0,esk5_0,k3_lattices(esk3_0,esk4_0,esk5_0)) = esk5_0
    | ~ l2_lattices(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_84]),c_0_38]),c_0_37])])).

cnf(c_0_93,negated_conjecture,
    ( k4_lattices(esk3_0,k3_lattices(esk3_0,esk4_0,esk5_0),esk5_0) = k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_77]),c_0_37]),c_0_38])])).

cnf(c_0_94,negated_conjecture,
    ( k4_lattices(esk3_0,esk6_0,k3_lattices(esk3_0,esk4_0,esk5_0)) = esk6_0
    | ~ l1_lattices(esk3_0)
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_86]),c_0_87]),c_0_26]),c_0_29])]),c_0_18])).

cnf(c_0_95,negated_conjecture,
    ( k4_lattices(esk3_0,esk6_0,k3_lattices(esk3_0,esk4_0,esk5_0)) = k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,esk4_0,esk5_0))
    | ~ l1_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_88]),c_0_26]),c_0_87]),c_0_29])]),c_0_18])).

cnf(c_0_96,negated_conjecture,
    ( k4_lattices(esk3_0,k3_lattices(esk3_0,esk4_0,esk5_0),k3_lattices(esk3_0,esk5_0,esk6_0)) = k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91]),c_0_37]),c_0_26])])).

cnf(c_0_97,negated_conjecture,
    ( k4_lattices(esk3_0,k3_lattices(esk3_0,X1,esk5_0),k3_lattices(esk3_0,esk5_0,X2)) = k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_84]),c_0_53]),c_0_38]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_98,negated_conjecture,
    ( k4_lattices(esk3_0,esk5_0,k3_lattices(esk3_0,esk4_0,esk5_0)) = esk5_0
    | ~ l1_lattices(esk3_0)
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_92]),c_0_87]),c_0_38]),c_0_29])]),c_0_18])).

cnf(c_0_99,negated_conjecture,
    ( k4_lattices(esk3_0,esk5_0,k3_lattices(esk3_0,esk4_0,esk5_0)) = k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0))
    | ~ l1_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_93]),c_0_38]),c_0_87]),c_0_29])]),c_0_18])).

cnf(c_0_100,negated_conjecture,
    ( k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,esk4_0,esk5_0)) = esk6_0
    | ~ l1_lattices(esk3_0)
    | ~ l2_lattices(esk3_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,esk4_0,esk5_0)) = k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_78]),c_0_26]),c_0_37])])).

cnf(c_0_102,negated_conjecture,
    ( k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0)) = esk5_0
    | ~ l1_lattices(esk3_0)
    | ~ l2_lattices(esk3_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0)) = esk6_0
    | ~ l1_lattices(esk3_0)
    | ~ l2_lattices(esk3_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_104,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_105,negated_conjecture,
    ( ~ l1_lattices(esk3_0)
    | ~ l2_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104])).

cnf(c_0_106,negated_conjecture,
    ( ~ l2_lattices(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_55]),c_0_17])])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_42]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.38/0.60  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.38/0.60  # and selection function PSelectComplexExceptRRHorn.
% 0.38/0.60  #
% 0.38/0.60  # Preprocessing time       : 0.029 s
% 0.38/0.60  # Presaturation interreduction done
% 0.38/0.60  
% 0.38/0.60  # Proof found!
% 0.38/0.60  # SZS status Theorem
% 0.38/0.60  # SZS output start CNFRefutation
% 0.38/0.60  fof(t32_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((k4_lattices(X1,X2,X3)=k4_lattices(X1,X2,X4)&k3_lattices(X1,X2,X3)=k3_lattices(X1,X2,X4))=>X3=X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_lattices)).
% 0.38/0.60  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.38/0.60  fof(t17_lattices, axiom, ![X1]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k1_lattices(X1,X2,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_lattices)).
% 0.38/0.60  fof(redefinition_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 0.38/0.60  fof(commutativity_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 0.38/0.60  fof(d9_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v9_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattices)).
% 0.38/0.60  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.38/0.60  fof(redefinition_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 0.38/0.60  fof(t31_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>k3_lattices(X1,X2,k4_lattices(X1,X3,X4))=k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_lattices)).
% 0.38/0.60  fof(commutativity_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 0.38/0.60  fof(dt_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k3_lattices(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_lattices)).
% 0.38/0.60  fof(c_0_11, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((k4_lattices(X1,X2,X3)=k4_lattices(X1,X2,X4)&k3_lattices(X1,X2,X3)=k3_lattices(X1,X2,X4))=>X3=X4)))))), inference(assume_negation,[status(cth)],[t32_lattices])).
% 0.38/0.60  fof(c_0_12, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.38/0.60  fof(c_0_13, negated_conjecture, ((((~v2_struct_0(esk3_0)&v10_lattices(esk3_0))&v11_lattices(esk3_0))&l3_lattices(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&((k4_lattices(esk3_0,esk4_0,esk5_0)=k4_lattices(esk3_0,esk4_0,esk6_0)&k3_lattices(esk3_0,esk4_0,esk5_0)=k3_lattices(esk3_0,esk4_0,esk6_0))&esk5_0!=esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.38/0.60  fof(c_0_14, plain, ![X27, X28]:(v2_struct_0(X27)|~v6_lattices(X27)|~v8_lattices(X27)|~v9_lattices(X27)|~l3_lattices(X27)|(~m1_subset_1(X28,u1_struct_0(X27))|k1_lattices(X27,X28,X28)=X28)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_lattices])])])])).
% 0.38/0.60  cnf(c_0_15, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.38/0.60  cnf(c_0_16, negated_conjecture, (v10_lattices(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.60  cnf(c_0_17, negated_conjecture, (l3_lattices(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.60  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.60  cnf(c_0_19, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.38/0.60  cnf(c_0_20, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.38/0.60  fof(c_0_21, plain, ![X21, X22, X23]:(v2_struct_0(X21)|~v4_lattices(X21)|~l2_lattices(X21)|~m1_subset_1(X22,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|k3_lattices(X21,X22,X23)=k1_lattices(X21,X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).
% 0.38/0.60  cnf(c_0_22, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.38/0.60  fof(c_0_23, plain, ![X6, X7, X8]:(v2_struct_0(X6)|~v4_lattices(X6)|~l2_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))|k3_lattices(X6,X7,X8)=k3_lattices(X6,X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).
% 0.38/0.60  fof(c_0_24, plain, ![X12, X13, X14]:((~v9_lattices(X12)|(~m1_subset_1(X13,u1_struct_0(X12))|(~m1_subset_1(X14,u1_struct_0(X12))|k2_lattices(X12,X13,k1_lattices(X12,X13,X14))=X13))|(v2_struct_0(X12)|~l3_lattices(X12)))&((m1_subset_1(esk1_1(X12),u1_struct_0(X12))|v9_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))&((m1_subset_1(esk2_1(X12),u1_struct_0(X12))|v9_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))&(k2_lattices(X12,esk1_1(X12),k1_lattices(X12,esk1_1(X12),esk2_1(X12)))!=esk1_1(X12)|v9_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).
% 0.38/0.60  cnf(c_0_25, plain, (v2_struct_0(X1)|k1_lattices(X1,X2,X2)=X2|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.38/0.60  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.60  cnf(c_0_27, negated_conjecture, (v9_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_28, negated_conjecture, (v8_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_16]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_29, negated_conjecture, (v6_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_16]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_30, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.60  cnf(c_0_31, negated_conjecture, (v4_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_16]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_32, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.38/0.60  fof(c_0_33, plain, ![X20]:((l1_lattices(X20)|~l3_lattices(X20))&(l2_lattices(X20)|~l3_lattices(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.38/0.60  fof(c_0_34, plain, ![X24, X25, X26]:(v2_struct_0(X24)|~v6_lattices(X24)|~l1_lattices(X24)|~m1_subset_1(X25,u1_struct_0(X24))|~m1_subset_1(X26,u1_struct_0(X24))|k4_lattices(X24,X25,X26)=k2_lattices(X24,X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).
% 0.38/0.60  cnf(c_0_35, plain, (k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2|v2_struct_0(X1)|~v9_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.38/0.60  cnf(c_0_36, negated_conjecture, (k1_lattices(esk3_0,esk6_0,esk6_0)=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.60  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.60  cnf(c_0_39, negated_conjecture, (k1_lattices(esk3_0,X1,esk6_0)=k3_lattices(esk3_0,X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_26]), c_0_31])]), c_0_18])).
% 0.38/0.60  fof(c_0_40, plain, ![X29, X30, X31, X32]:(v2_struct_0(X29)|~v10_lattices(X29)|~v11_lattices(X29)|~l3_lattices(X29)|(~m1_subset_1(X30,u1_struct_0(X29))|(~m1_subset_1(X31,u1_struct_0(X29))|(~m1_subset_1(X32,u1_struct_0(X29))|k3_lattices(X29,X30,k4_lattices(X29,X31,X32))=k4_lattices(X29,k3_lattices(X29,X30,X31),k3_lattices(X29,X30,X32)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t31_lattices])])])])).
% 0.38/0.60  cnf(c_0_41, negated_conjecture, (k3_lattices(esk3_0,X1,esk6_0)=k3_lattices(esk3_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_26]), c_0_31])]), c_0_18])).
% 0.38/0.60  cnf(c_0_42, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.38/0.60  cnf(c_0_43, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.38/0.60  cnf(c_0_44, negated_conjecture, (k2_lattices(esk3_0,esk6_0,esk6_0)=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_26]), c_0_27]), c_0_17])]), c_0_18])).
% 0.38/0.60  fof(c_0_45, plain, ![X9, X10, X11]:(v2_struct_0(X9)|~v6_lattices(X9)|~l1_lattices(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))|k4_lattices(X9,X10,X11)=k4_lattices(X9,X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).
% 0.38/0.60  cnf(c_0_46, negated_conjecture, (k1_lattices(esk3_0,esk4_0,esk4_0)=esk4_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_37]), c_0_27]), c_0_28]), c_0_29]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_47, negated_conjecture, (k1_lattices(esk3_0,esk5_0,esk5_0)=esk5_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_38]), c_0_27]), c_0_28]), c_0_29]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_48, negated_conjecture, (k1_lattices(esk3_0,X1,esk5_0)=k3_lattices(esk3_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_38]), c_0_31])]), c_0_18])).
% 0.38/0.60  fof(c_0_49, plain, ![X17, X18, X19]:(v2_struct_0(X17)|~v4_lattices(X17)|~l2_lattices(X17)|~m1_subset_1(X18,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|m1_subset_1(k3_lattices(X17,X18,X19),u1_struct_0(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_lattices])])])).
% 0.38/0.60  cnf(c_0_50, negated_conjecture, (k3_lattices(esk3_0,esk6_0,esk6_0)=esk6_0|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_39]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_51, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,k4_lattices(X1,X3,X4))=k4_lattices(X1,k3_lattices(X1,X2,X3),k3_lattices(X1,X2,X4))|~v10_lattices(X1)|~v11_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.38/0.60  cnf(c_0_52, negated_conjecture, (k3_lattices(esk3_0,X1,esk6_0)=k3_lattices(esk3_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_17])])).
% 0.38/0.60  cnf(c_0_53, negated_conjecture, (v11_lattices(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.60  cnf(c_0_54, negated_conjecture, (k4_lattices(esk3_0,esk6_0,esk6_0)=esk6_0|~l1_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_26]), c_0_29])]), c_0_18])).
% 0.38/0.60  cnf(c_0_55, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.38/0.60  cnf(c_0_56, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.38/0.60  cnf(c_0_57, negated_conjecture, (k2_lattices(esk3_0,esk4_0,esk4_0)=esk4_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_46]), c_0_37]), c_0_27]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_58, negated_conjecture, (k2_lattices(esk3_0,esk5_0,esk5_0)=esk5_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_47]), c_0_38]), c_0_27]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_59, negated_conjecture, (k3_lattices(esk3_0,esk5_0,esk5_0)=esk5_0|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_48]), c_0_38]), c_0_27]), c_0_28]), c_0_29]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_60, negated_conjecture, (k1_lattices(esk3_0,X1,esk4_0)=k3_lattices(esk3_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_37]), c_0_31])]), c_0_18])).
% 0.38/0.60  cnf(c_0_61, plain, (v2_struct_0(X1)|m1_subset_1(k3_lattices(X1,X2,X3),u1_struct_0(X1))|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.38/0.60  cnf(c_0_62, negated_conjecture, (k3_lattices(esk3_0,esk4_0,esk5_0)=k3_lattices(esk3_0,esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.60  cnf(c_0_63, negated_conjecture, (k3_lattices(esk3_0,esk6_0,esk6_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_42]), c_0_17])])).
% 0.38/0.60  cnf(c_0_64, negated_conjecture, (k3_lattices(esk3_0,X1,esk4_0)=k3_lattices(esk3_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_37]), c_0_31])]), c_0_18])).
% 0.38/0.60  cnf(c_0_65, negated_conjecture, (k4_lattices(esk3_0,k3_lattices(esk3_0,X1,X2),k3_lattices(esk3_0,esk6_0,X1))=k3_lattices(esk3_0,X1,k4_lattices(esk3_0,X2,esk6_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_26]), c_0_16]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_66, negated_conjecture, (k4_lattices(esk3_0,k3_lattices(esk3_0,X1,esk6_0),k3_lattices(esk3_0,esk6_0,X2))=k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,X1,X2))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_26]), c_0_16]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_67, negated_conjecture, (k4_lattices(esk3_0,esk6_0,esk6_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_17])])).
% 0.38/0.60  cnf(c_0_68, negated_conjecture, (k4_lattices(esk3_0,X1,esk4_0)=k4_lattices(esk3_0,esk4_0,X1)|~l1_lattices(esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_37]), c_0_29])]), c_0_18])).
% 0.38/0.60  cnf(c_0_69, negated_conjecture, (k4_lattices(esk3_0,esk4_0,esk4_0)=esk4_0|~l1_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_57]), c_0_37]), c_0_29])]), c_0_18])).
% 0.38/0.60  cnf(c_0_70, negated_conjecture, (k4_lattices(esk3_0,X1,esk5_0)=k4_lattices(esk3_0,esk5_0,X1)|~l1_lattices(esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_38]), c_0_29])]), c_0_18])).
% 0.38/0.60  cnf(c_0_71, negated_conjecture, (k4_lattices(esk3_0,esk5_0,esk5_0)=esk5_0|~l1_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_58]), c_0_38]), c_0_29])]), c_0_18])).
% 0.38/0.60  cnf(c_0_72, negated_conjecture, (k3_lattices(esk3_0,X1,esk5_0)=k3_lattices(esk3_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_38]), c_0_31])]), c_0_18])).
% 0.38/0.60  cnf(c_0_73, negated_conjecture, (k3_lattices(esk3_0,esk5_0,esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_42]), c_0_17])])).
% 0.38/0.60  cnf(c_0_74, negated_conjecture, (k2_lattices(esk3_0,X1,k3_lattices(esk3_0,X1,esk4_0))=X1|~m1_subset_1(X1,u1_struct_0(esk3_0))|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_60]), c_0_37]), c_0_27]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_75, negated_conjecture, (m1_subset_1(k3_lattices(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_26]), c_0_37]), c_0_31])]), c_0_18])).
% 0.38/0.60  cnf(c_0_76, negated_conjecture, (k4_lattices(esk3_0,k3_lattices(esk3_0,esk6_0,X1),esk6_0)=k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,X1,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_63]), c_0_53]), c_0_26]), c_0_16]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_77, negated_conjecture, (k3_lattices(esk3_0,X1,esk4_0)=k3_lattices(esk3_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_42]), c_0_17])])).
% 0.38/0.60  cnf(c_0_78, negated_conjecture, (k4_lattices(esk3_0,esk4_0,esk5_0)=k4_lattices(esk3_0,esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.60  cnf(c_0_79, negated_conjecture, (k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,X1,X1))=k3_lattices(esk3_0,X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_26])])).
% 0.38/0.60  cnf(c_0_80, negated_conjecture, (k4_lattices(esk3_0,X1,esk4_0)=k4_lattices(esk3_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_55]), c_0_17])])).
% 0.38/0.60  cnf(c_0_81, negated_conjecture, (k4_lattices(esk3_0,esk4_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_55]), c_0_17])])).
% 0.38/0.60  cnf(c_0_82, negated_conjecture, (k4_lattices(esk3_0,X1,esk5_0)=k4_lattices(esk3_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_55]), c_0_17])])).
% 0.38/0.60  cnf(c_0_83, negated_conjecture, (k4_lattices(esk3_0,esk5_0,esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_55]), c_0_17])])).
% 0.38/0.60  cnf(c_0_84, negated_conjecture, (k3_lattices(esk3_0,X1,esk5_0)=k3_lattices(esk3_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_42]), c_0_17])])).
% 0.38/0.60  cnf(c_0_85, negated_conjecture, (k4_lattices(esk3_0,k3_lattices(esk3_0,esk5_0,X1),esk5_0)=k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,X1,esk5_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_73]), c_0_53]), c_0_38]), c_0_16]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_86, negated_conjecture, (k2_lattices(esk3_0,esk6_0,k3_lattices(esk3_0,esk4_0,esk5_0))=esk6_0|~l2_lattices(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_52]), c_0_62]), c_0_26]), c_0_37])])).
% 0.38/0.60  cnf(c_0_87, negated_conjecture, (m1_subset_1(k3_lattices(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_42]), c_0_17])])).
% 0.38/0.60  cnf(c_0_88, negated_conjecture, (k4_lattices(esk3_0,k3_lattices(esk3_0,esk4_0,esk5_0),esk6_0)=k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_62]), c_0_78]), c_0_37]), c_0_26])])).
% 0.38/0.60  cnf(c_0_89, negated_conjecture, (k4_lattices(esk3_0,k3_lattices(esk3_0,X1,X2),k3_lattices(esk3_0,X1,esk5_0))=k3_lattices(esk3_0,X1,k4_lattices(esk3_0,X2,esk5_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_38]), c_0_53]), c_0_16]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_90, negated_conjecture, (k3_lattices(esk3_0,esk6_0,esk4_0)=k3_lattices(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81]), c_0_62]), c_0_37])])).
% 0.38/0.60  cnf(c_0_91, negated_conjecture, (k3_lattices(esk3_0,esk6_0,esk5_0)=k3_lattices(esk3_0,esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_82]), c_0_83]), c_0_38])])).
% 0.38/0.60  cnf(c_0_92, negated_conjecture, (k2_lattices(esk3_0,esk5_0,k3_lattices(esk3_0,esk4_0,esk5_0))=esk5_0|~l2_lattices(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_84]), c_0_38]), c_0_37])])).
% 0.38/0.60  cnf(c_0_93, negated_conjecture, (k4_lattices(esk3_0,k3_lattices(esk3_0,esk4_0,esk5_0),esk5_0)=k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_77]), c_0_37]), c_0_38])])).
% 0.38/0.60  cnf(c_0_94, negated_conjecture, (k4_lattices(esk3_0,esk6_0,k3_lattices(esk3_0,esk4_0,esk5_0))=esk6_0|~l1_lattices(esk3_0)|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_86]), c_0_87]), c_0_26]), c_0_29])]), c_0_18])).
% 0.38/0.60  cnf(c_0_95, negated_conjecture, (k4_lattices(esk3_0,esk6_0,k3_lattices(esk3_0,esk4_0,esk5_0))=k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,esk4_0,esk5_0))|~l1_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_88]), c_0_26]), c_0_87]), c_0_29])]), c_0_18])).
% 0.38/0.60  cnf(c_0_96, negated_conjecture, (k4_lattices(esk3_0,k3_lattices(esk3_0,esk4_0,esk5_0),k3_lattices(esk3_0,esk5_0,esk6_0))=k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91]), c_0_37]), c_0_26])])).
% 0.38/0.60  cnf(c_0_97, negated_conjecture, (k4_lattices(esk3_0,k3_lattices(esk3_0,X1,esk5_0),k3_lattices(esk3_0,esk5_0,X2))=k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,X1,X2))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_84]), c_0_53]), c_0_38]), c_0_16]), c_0_17])]), c_0_18])).
% 0.38/0.60  cnf(c_0_98, negated_conjecture, (k4_lattices(esk3_0,esk5_0,k3_lattices(esk3_0,esk4_0,esk5_0))=esk5_0|~l1_lattices(esk3_0)|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_92]), c_0_87]), c_0_38]), c_0_29])]), c_0_18])).
% 0.38/0.60  cnf(c_0_99, negated_conjecture, (k4_lattices(esk3_0,esk5_0,k3_lattices(esk3_0,esk4_0,esk5_0))=k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0))|~l1_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_93]), c_0_38]), c_0_87]), c_0_29])]), c_0_18])).
% 0.38/0.60  cnf(c_0_100, negated_conjecture, (k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,esk4_0,esk5_0))=esk6_0|~l1_lattices(esk3_0)|~l2_lattices(esk3_0)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.38/0.60  cnf(c_0_101, negated_conjecture, (k3_lattices(esk3_0,esk6_0,k4_lattices(esk3_0,esk4_0,esk5_0))=k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_78]), c_0_26]), c_0_37])])).
% 0.38/0.60  cnf(c_0_102, negated_conjecture, (k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0))=esk5_0|~l1_lattices(esk3_0)|~l2_lattices(esk3_0)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.38/0.60  cnf(c_0_103, negated_conjecture, (k3_lattices(esk3_0,esk5_0,k4_lattices(esk3_0,esk4_0,esk5_0))=esk6_0|~l1_lattices(esk3_0)|~l2_lattices(esk3_0)), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.38/0.60  cnf(c_0_104, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.38/0.60  cnf(c_0_105, negated_conjecture, (~l1_lattices(esk3_0)|~l2_lattices(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104])).
% 0.38/0.60  cnf(c_0_106, negated_conjecture, (~l2_lattices(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_55]), c_0_17])])).
% 0.38/0.60  cnf(c_0_107, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_42]), c_0_17])]), ['proof']).
% 0.38/0.60  # SZS output end CNFRefutation
% 0.38/0.60  # Proof object total steps             : 108
% 0.38/0.60  # Proof object clause steps            : 85
% 0.38/0.60  # Proof object formula steps           : 23
% 0.38/0.60  # Proof object conjectures             : 74
% 0.38/0.60  # Proof object clause conjectures      : 71
% 0.38/0.60  # Proof object formula conjectures     : 3
% 0.38/0.60  # Proof object initial clauses used    : 24
% 0.38/0.60  # Proof object initial formulas used   : 11
% 0.38/0.60  # Proof object generating inferences   : 61
% 0.38/0.60  # Proof object simplifying inferences  : 220
% 0.38/0.60  # Training examples: 0 positive, 0 negative
% 0.38/0.60  # Parsed axioms                        : 11
% 0.38/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.60  # Initial clauses                      : 30
% 0.38/0.60  # Removed in clause preprocessing      : 1
% 0.38/0.60  # Initial clauses in saturation        : 29
% 0.38/0.60  # Processed clauses                    : 1231
% 0.38/0.60  # ...of these trivial                  : 18
% 0.38/0.60  # ...subsumed                          : 708
% 0.38/0.60  # ...remaining for further processing  : 505
% 0.38/0.60  # Other redundant clauses eliminated   : 0
% 0.38/0.60  # Clauses deleted for lack of memory   : 0
% 0.38/0.60  # Backward-subsumed                    : 108
% 0.38/0.60  # Backward-rewritten                   : 60
% 0.38/0.60  # Generated clauses                    : 6953
% 0.38/0.60  # ...of the previous two non-trivial   : 6317
% 0.38/0.60  # Contextual simplify-reflections      : 4
% 0.38/0.60  # Paramodulations                      : 6953
% 0.38/0.60  # Factorizations                       : 0
% 0.38/0.60  # Equation resolutions                 : 0
% 0.38/0.60  # Propositional unsat checks           : 0
% 0.38/0.60  #    Propositional check models        : 0
% 0.38/0.60  #    Propositional check unsatisfiable : 0
% 0.38/0.60  #    Propositional clauses             : 0
% 0.38/0.60  #    Propositional clauses after purity: 0
% 0.38/0.60  #    Propositional unsat core size     : 0
% 0.38/0.60  #    Propositional preprocessing time  : 0.000
% 0.38/0.60  #    Propositional encoding time       : 0.000
% 0.38/0.60  #    Propositional solver time         : 0.000
% 0.38/0.60  #    Success case prop preproc time    : 0.000
% 0.38/0.60  #    Success case prop encoding time   : 0.000
% 0.38/0.60  #    Success case prop solver time     : 0.000
% 0.38/0.60  # Current number of processed clauses  : 308
% 0.38/0.60  #    Positive orientable unit clauses  : 76
% 0.38/0.60  #    Positive unorientable unit clauses: 0
% 0.38/0.60  #    Negative unit clauses             : 3
% 0.38/0.60  #    Non-unit-clauses                  : 229
% 0.38/0.60  # Current number of unprocessed clauses: 5095
% 0.38/0.60  # ...number of literals in the above   : 22960
% 0.38/0.60  # Current number of archived formulas  : 0
% 0.38/0.60  # Current number of archived clauses   : 197
% 0.38/0.60  # Clause-clause subsumption calls (NU) : 12932
% 0.38/0.60  # Rec. Clause-clause subsumption calls : 9221
% 0.38/0.60  # Non-unit clause-clause subsumptions  : 797
% 0.38/0.60  # Unit Clause-clause subsumption calls : 379
% 0.38/0.60  # Rewrite failures with RHS unbound    : 0
% 0.38/0.60  # BW rewrite match attempts            : 772
% 0.38/0.60  # BW rewrite match successes           : 46
% 0.38/0.60  # Condensation attempts                : 0
% 0.38/0.60  # Condensation successes               : 0
% 0.38/0.60  # Termbank termtop insertions          : 260515
% 0.38/0.60  
% 0.38/0.60  # -------------------------------------------------
% 0.38/0.60  # User time                : 0.248 s
% 0.38/0.60  # System time              : 0.012 s
% 0.38/0.60  # Total time               : 0.260 s
% 0.38/0.60  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
