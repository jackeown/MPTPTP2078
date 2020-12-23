%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:24 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   82 (1628 expanded)
%              Number of clauses        :   63 ( 541 expanded)
%              Number of leaves         :    9 ( 398 expanded)
%              Depth                    :   13
%              Number of atoms          :  315 (11974 expanded)
%              Number of equality atoms :   68 (2859 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_lattices)).

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

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(t18_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattices(X1,X2,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_lattices)).

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
    ( ~ v2_struct_0(esk6_0)
    & v10_lattices(esk6_0)
    & v11_lattices(esk6_0)
    & l3_lattices(esk6_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    & m1_subset_1(esk9_0,u1_struct_0(esk6_0))
    & k4_lattices(esk6_0,esk7_0,esk8_0) = k4_lattices(esk6_0,esk7_0,esk9_0)
    & k3_lattices(esk6_0,esk7_0,esk8_0) = k3_lattices(esk6_0,esk7_0,esk9_0)
    & esk8_0 != esk9_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X25,X26,X27] :
      ( v2_struct_0(X25)
      | ~ v6_lattices(X25)
      | ~ l1_lattices(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ m1_subset_1(X27,u1_struct_0(X25))
      | k4_lattices(X25,X26,X27) = k2_lattices(X25,X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

cnf(c_0_13,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v10_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l3_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v6_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])]),c_0_16])).

fof(c_0_20,plain,(
    ! [X21] :
      ( ( l1_lattices(X21)
        | ~ l3_lattices(X21) )
      & ( l2_lattices(X21)
        | ~ l3_lattices(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_21,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk9_0) = k2_lattices(esk6_0,X1,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l1_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),c_0_16])).

cnf(c_0_22,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_24,plain,(
    ! [X22,X23,X24] :
      ( v2_struct_0(X22)
      | ~ v4_lattices(X22)
      | ~ l2_lattices(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | ~ m1_subset_1(X24,u1_struct_0(X22))
      | k3_lattices(X22,X23,X24) = k1_lattices(X22,X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

cnf(c_0_25,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_26,plain,(
    ! [X6,X7,X8] :
      ( v2_struct_0(X6)
      | ~ v6_lattices(X6)
      | ~ l1_lattices(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | k4_lattices(X6,X7,X8) = k4_lattices(X6,X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_27,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,esk8_0) = k4_lattices(esk6_0,esk7_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk9_0) = k2_lattices(esk6_0,X1,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_15])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk8_0) = k2_lattices(esk6_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l1_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_23]),c_0_19])]),c_0_16])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( v4_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,esk8_0) = k2_lattices(esk6_0,esk7_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_35,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk8_0) = k2_lattices(esk6_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_22]),c_0_15])])).

fof(c_0_36,plain,(
    ! [X28,X29] :
      ( v2_struct_0(X28)
      | ~ v6_lattices(X28)
      | ~ v8_lattices(X28)
      | ~ v9_lattices(X28)
      | ~ l3_lattices(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | k4_lattices(X28,X29,X29) = X29 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t18_lattices])])])])).

cnf(c_0_37,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_39,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v8_lattices(X16)
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | k1_lattices(X16,k2_lattices(X16,X17,X18),X18) = X18
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( m1_subset_1(esk4_1(X16),u1_struct_0(X16))
        | v8_lattices(X16)
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( m1_subset_1(esk5_1(X16),u1_struct_0(X16))
        | v8_lattices(X16)
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) )
      & ( k1_lattices(X16,k2_lattices(X16,esk4_1(X16),esk5_1(X16)),esk5_1(X16)) != esk5_1(X16)
        | v8_lattices(X16)
        | v2_struct_0(X16)
        | ~ l3_lattices(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).

cnf(c_0_40,negated_conjecture,
    ( k3_lattices(esk6_0,esk7_0,esk8_0) = k3_lattices(esk6_0,esk7_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_41,negated_conjecture,
    ( k3_lattices(esk6_0,X1,esk9_0) = k1_lattices(esk6_0,X1,esk9_0)
    | ~ l2_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_18]),c_0_32])]),c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk9_0) = k4_lattices(esk6_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l1_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_18]),c_0_19])]),c_0_16])).

fof(c_0_43,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ v11_lattices(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | k2_lattices(X9,X10,k1_lattices(X9,X11,X12)) = k1_lattices(X9,k2_lattices(X9,X10,X11),k2_lattices(X9,X10,X12))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk1_1(X9),u1_struct_0(X9))
        | v11_lattices(X9)
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk2_1(X9),u1_struct_0(X9))
        | v11_lattices(X9)
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk3_1(X9),u1_struct_0(X9))
        | v11_lattices(X9)
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( k2_lattices(X9,esk1_1(X9),k1_lattices(X9,esk2_1(X9),esk3_1(X9))) != k1_lattices(X9,k2_lattices(X9,esk1_1(X9),esk2_1(X9)),k2_lattices(X9,esk1_1(X9),esk3_1(X9)))
        | v11_lattices(X9)
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_lattices])])])])])])).

cnf(c_0_44,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk7_0) = k2_lattices(esk6_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l1_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_29]),c_0_19])]),c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,esk9_0) = k2_lattices(esk6_0,esk7_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,esk9_0) = k2_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_29])])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X2) = X2
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( v9_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( v8_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_50,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( k3_lattices(esk6_0,esk7_0,esk8_0) = k1_lattices(esk6_0,esk7_0,esk9_0)
    | ~ l2_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_29])])).

cnf(c_0_52,negated_conjecture,
    ( k3_lattices(esk6_0,X1,esk8_0) = k1_lattices(esk6_0,X1,esk8_0)
    | ~ l2_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_23]),c_0_32])]),c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk8_0) = k4_lattices(esk6_0,esk8_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l1_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_23]),c_0_19])]),c_0_16])).

cnf(c_0_54,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk9_0) = k4_lattices(esk6_0,esk9_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_22]),c_0_15])])).

cnf(c_0_55,plain,
    ( k2_lattices(X1,X2,k1_lattices(X1,X3,X4)) = k1_lattices(X1,k2_lattices(X1,X2,X3),k2_lattices(X1,X2,X4))
    | v2_struct_0(X1)
    | ~ v11_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( v11_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_57,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk7_0) = k2_lattices(esk6_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_22]),c_0_15])])).

cnf(c_0_58,negated_conjecture,
    ( k4_lattices(esk6_0,esk7_0,esk9_0) = k2_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( k4_lattices(esk6_0,esk9_0,esk9_0) = esk9_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_18]),c_0_48]),c_0_49]),c_0_19]),c_0_15])]),c_0_16])).

cnf(c_0_60,negated_conjecture,
    ( k1_lattices(esk6_0,k2_lattices(esk6_0,X1,esk9_0),esk9_0) = esk9_0
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_18]),c_0_49]),c_0_15])]),c_0_16])).

cnf(c_0_61,negated_conjecture,
    ( k1_lattices(esk6_0,esk7_0,esk9_0) = k1_lattices(esk6_0,esk7_0,esk8_0)
    | ~ l2_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_29])])).

cnf(c_0_62,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_63,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk8_0) = k4_lattices(esk6_0,esk8_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_22]),c_0_15])])).

cnf(c_0_64,negated_conjecture,
    ( k4_lattices(esk6_0,esk8_0,esk8_0) = esk8_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_23]),c_0_48]),c_0_49]),c_0_19]),c_0_15])]),c_0_16])).

cnf(c_0_65,negated_conjecture,
    ( k4_lattices(esk6_0,esk8_0,esk9_0) = k2_lattices(esk6_0,esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_54]),c_0_18]),c_0_23])])).

cnf(c_0_66,negated_conjecture,
    ( k1_lattices(esk6_0,k2_lattices(esk6_0,X1,X2),k2_lattices(esk6_0,X1,esk9_0)) = k2_lattices(esk6_0,X1,k1_lattices(esk6_0,X2,esk9_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_18]),c_0_56]),c_0_15])]),c_0_16])).

cnf(c_0_67,negated_conjecture,
    ( k2_lattices(esk6_0,esk9_0,esk7_0) = k2_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_54]),c_0_58]),c_0_18]),c_0_29])])).

cnf(c_0_68,negated_conjecture,
    ( k2_lattices(esk6_0,esk9_0,esk9_0) = esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_28]),c_0_18])])).

cnf(c_0_69,negated_conjecture,
    ( k1_lattices(esk6_0,k2_lattices(esk6_0,esk7_0,esk8_0),esk9_0) = esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_46]),c_0_29])])).

cnf(c_0_70,negated_conjecture,
    ( k1_lattices(esk6_0,esk7_0,esk9_0) = k1_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_15])])).

cnf(c_0_71,negated_conjecture,
    ( k1_lattices(esk6_0,k2_lattices(esk6_0,X1,X2),k2_lattices(esk6_0,X1,esk8_0)) = k2_lattices(esk6_0,X1,k1_lattices(esk6_0,X2,esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_23]),c_0_56]),c_0_15])]),c_0_16])).

cnf(c_0_72,negated_conjecture,
    ( k2_lattices(esk6_0,esk8_0,esk7_0) = k2_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_63]),c_0_34]),c_0_46]),c_0_23]),c_0_29])])).

cnf(c_0_73,negated_conjecture,
    ( k2_lattices(esk6_0,esk8_0,esk8_0) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_35]),c_0_23])])).

cnf(c_0_74,negated_conjecture,
    ( k2_lattices(esk6_0,esk9_0,esk8_0) = k2_lattices(esk6_0,esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_65]),c_0_23])])).

cnf(c_0_75,negated_conjecture,
    ( k2_lattices(esk6_0,esk9_0,k1_lattices(esk6_0,esk7_0,esk8_0)) = esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69]),c_0_70]),c_0_29]),c_0_18])])).

cnf(c_0_76,negated_conjecture,
    ( k1_lattices(esk6_0,k2_lattices(esk6_0,X1,esk8_0),esk8_0) = esk8_0
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_23]),c_0_49]),c_0_15])]),c_0_16])).

cnf(c_0_77,negated_conjecture,
    ( k1_lattices(esk6_0,k2_lattices(esk6_0,esk7_0,esk8_0),esk8_0) = k2_lattices(esk6_0,esk8_0,k1_lattices(esk6_0,esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_29]),c_0_23])])).

cnf(c_0_78,negated_conjecture,
    ( k1_lattices(esk6_0,k2_lattices(esk6_0,esk7_0,esk8_0),k2_lattices(esk6_0,esk8_0,esk9_0)) = esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_67]),c_0_74]),c_0_75]),c_0_29]),c_0_18])])).

cnf(c_0_79,negated_conjecture,
    ( k2_lattices(esk6_0,esk8_0,k1_lattices(esk6_0,esk7_0,esk8_0)) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_29])])).

cnf(c_0_80,negated_conjecture,
    ( esk8_0 != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_72]),c_0_70]),c_0_29]),c_0_23])]),c_0_78]),c_0_79]),c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:00:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.029 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t32_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((k4_lattices(X1,X2,X3)=k4_lattices(X1,X2,X4)&k3_lattices(X1,X2,X3)=k3_lattices(X1,X2,X4))=>X3=X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_lattices)).
% 0.12/0.38  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.12/0.38  fof(redefinition_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 0.12/0.38  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.12/0.38  fof(redefinition_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 0.12/0.38  fof(commutativity_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 0.12/0.38  fof(t18_lattices, axiom, ![X1]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,X2,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_lattices)).
% 0.12/0.38  fof(d8_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v8_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattices)).
% 0.12/0.38  fof(d11_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v11_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>k2_lattices(X1,X2,k1_lattices(X1,X3,X4))=k1_lattices(X1,k2_lattices(X1,X2,X3),k2_lattices(X1,X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_lattices)).
% 0.12/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((k4_lattices(X1,X2,X3)=k4_lattices(X1,X2,X4)&k3_lattices(X1,X2,X3)=k3_lattices(X1,X2,X4))=>X3=X4)))))), inference(assume_negation,[status(cth)],[t32_lattices])).
% 0.12/0.38  fof(c_0_10, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.12/0.38  fof(c_0_11, negated_conjecture, ((((~v2_struct_0(esk6_0)&v10_lattices(esk6_0))&v11_lattices(esk6_0))&l3_lattices(esk6_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&(m1_subset_1(esk8_0,u1_struct_0(esk6_0))&(m1_subset_1(esk9_0,u1_struct_0(esk6_0))&((k4_lattices(esk6_0,esk7_0,esk8_0)=k4_lattices(esk6_0,esk7_0,esk9_0)&k3_lattices(esk6_0,esk7_0,esk8_0)=k3_lattices(esk6_0,esk7_0,esk9_0))&esk8_0!=esk9_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.12/0.38  fof(c_0_12, plain, ![X25, X26, X27]:(v2_struct_0(X25)|~v6_lattices(X25)|~l1_lattices(X25)|~m1_subset_1(X26,u1_struct_0(X25))|~m1_subset_1(X27,u1_struct_0(X25))|k4_lattices(X25,X26,X27)=k2_lattices(X25,X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).
% 0.12/0.38  cnf(c_0_13, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_14, negated_conjecture, (v10_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_15, negated_conjecture, (l3_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_17, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (v6_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])]), c_0_16])).
% 0.12/0.38  fof(c_0_20, plain, ![X21]:((l1_lattices(X21)|~l3_lattices(X21))&(l2_lattices(X21)|~l3_lattices(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.12/0.38  cnf(c_0_21, negated_conjecture, (k4_lattices(esk6_0,X1,esk9_0)=k2_lattices(esk6_0,X1,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~l1_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])]), c_0_16])).
% 0.12/0.38  cnf(c_0_22, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  fof(c_0_24, plain, ![X22, X23, X24]:(v2_struct_0(X22)|~v4_lattices(X22)|~l2_lattices(X22)|~m1_subset_1(X23,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|k3_lattices(X22,X23,X24)=k1_lattices(X22,X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).
% 0.12/0.38  cnf(c_0_25, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  fof(c_0_26, plain, ![X6, X7, X8]:(v2_struct_0(X6)|~v6_lattices(X6)|~l1_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))|k4_lattices(X6,X7,X8)=k4_lattices(X6,X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (k4_lattices(esk6_0,esk7_0,esk8_0)=k4_lattices(esk6_0,esk7_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_28, negated_conjecture, (k4_lattices(esk6_0,X1,esk9_0)=k2_lattices(esk6_0,X1,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_15])])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (k4_lattices(esk6_0,X1,esk8_0)=k2_lattices(esk6_0,X1,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~l1_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_23]), c_0_19])]), c_0_16])).
% 0.12/0.38  cnf(c_0_31, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (v4_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_14]), c_0_15])]), c_0_16])).
% 0.12/0.38  cnf(c_0_33, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (k4_lattices(esk6_0,esk7_0,esk8_0)=k2_lattices(esk6_0,esk7_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.12/0.38  cnf(c_0_35, negated_conjecture, (k4_lattices(esk6_0,X1,esk8_0)=k2_lattices(esk6_0,X1,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_22]), c_0_15])])).
% 0.12/0.38  fof(c_0_36, plain, ![X28, X29]:(v2_struct_0(X28)|~v6_lattices(X28)|~v8_lattices(X28)|~v9_lattices(X28)|~l3_lattices(X28)|(~m1_subset_1(X29,u1_struct_0(X28))|k4_lattices(X28,X29,X29)=X29)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t18_lattices])])])])).
% 0.12/0.38  cnf(c_0_37, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_38, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  fof(c_0_39, plain, ![X16, X17, X18]:((~v8_lattices(X16)|(~m1_subset_1(X17,u1_struct_0(X16))|(~m1_subset_1(X18,u1_struct_0(X16))|k1_lattices(X16,k2_lattices(X16,X17,X18),X18)=X18))|(v2_struct_0(X16)|~l3_lattices(X16)))&((m1_subset_1(esk4_1(X16),u1_struct_0(X16))|v8_lattices(X16)|(v2_struct_0(X16)|~l3_lattices(X16)))&((m1_subset_1(esk5_1(X16),u1_struct_0(X16))|v8_lattices(X16)|(v2_struct_0(X16)|~l3_lattices(X16)))&(k1_lattices(X16,k2_lattices(X16,esk4_1(X16),esk5_1(X16)),esk5_1(X16))!=esk5_1(X16)|v8_lattices(X16)|(v2_struct_0(X16)|~l3_lattices(X16)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (k3_lattices(esk6_0,esk7_0,esk8_0)=k3_lattices(esk6_0,esk7_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (k3_lattices(esk6_0,X1,esk9_0)=k1_lattices(esk6_0,X1,esk9_0)|~l2_lattices(esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_18]), c_0_32])]), c_0_16])).
% 0.12/0.38  cnf(c_0_42, negated_conjecture, (k4_lattices(esk6_0,X1,esk9_0)=k4_lattices(esk6_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~l1_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_18]), c_0_19])]), c_0_16])).
% 0.12/0.38  fof(c_0_43, plain, ![X9, X10, X11, X12]:((~v11_lattices(X9)|(~m1_subset_1(X10,u1_struct_0(X9))|(~m1_subset_1(X11,u1_struct_0(X9))|(~m1_subset_1(X12,u1_struct_0(X9))|k2_lattices(X9,X10,k1_lattices(X9,X11,X12))=k1_lattices(X9,k2_lattices(X9,X10,X11),k2_lattices(X9,X10,X12)))))|(v2_struct_0(X9)|~l3_lattices(X9)))&((m1_subset_1(esk1_1(X9),u1_struct_0(X9))|v11_lattices(X9)|(v2_struct_0(X9)|~l3_lattices(X9)))&((m1_subset_1(esk2_1(X9),u1_struct_0(X9))|v11_lattices(X9)|(v2_struct_0(X9)|~l3_lattices(X9)))&((m1_subset_1(esk3_1(X9),u1_struct_0(X9))|v11_lattices(X9)|(v2_struct_0(X9)|~l3_lattices(X9)))&(k2_lattices(X9,esk1_1(X9),k1_lattices(X9,esk2_1(X9),esk3_1(X9)))!=k1_lattices(X9,k2_lattices(X9,esk1_1(X9),esk2_1(X9)),k2_lattices(X9,esk1_1(X9),esk3_1(X9)))|v11_lattices(X9)|(v2_struct_0(X9)|~l3_lattices(X9))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_lattices])])])])])])).
% 0.12/0.38  cnf(c_0_44, negated_conjecture, (k4_lattices(esk6_0,X1,esk7_0)=k2_lattices(esk6_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~l1_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_29]), c_0_19])]), c_0_16])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (k4_lattices(esk6_0,esk7_0,esk9_0)=k2_lattices(esk6_0,esk7_0,esk9_0)), inference(rw,[status(thm)],[c_0_27, c_0_34])).
% 0.12/0.38  cnf(c_0_46, negated_conjecture, (k2_lattices(esk6_0,esk7_0,esk9_0)=k2_lattices(esk6_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_29])])).
% 0.12/0.38  cnf(c_0_47, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X2)=X2|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.38  cnf(c_0_48, negated_conjecture, (v9_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_14]), c_0_15])]), c_0_16])).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, (v8_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_14]), c_0_15])]), c_0_16])).
% 0.12/0.38  cnf(c_0_50, plain, (k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3|v2_struct_0(X1)|~v8_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.38  cnf(c_0_51, negated_conjecture, (k3_lattices(esk6_0,esk7_0,esk8_0)=k1_lattices(esk6_0,esk7_0,esk9_0)|~l2_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_29])])).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (k3_lattices(esk6_0,X1,esk8_0)=k1_lattices(esk6_0,X1,esk8_0)|~l2_lattices(esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_23]), c_0_32])]), c_0_16])).
% 0.12/0.38  cnf(c_0_53, negated_conjecture, (k4_lattices(esk6_0,X1,esk8_0)=k4_lattices(esk6_0,esk8_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~l1_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_23]), c_0_19])]), c_0_16])).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, (k4_lattices(esk6_0,X1,esk9_0)=k4_lattices(esk6_0,esk9_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_22]), c_0_15])])).
% 0.12/0.38  cnf(c_0_55, plain, (k2_lattices(X1,X2,k1_lattices(X1,X3,X4))=k1_lattices(X1,k2_lattices(X1,X2,X3),k2_lattices(X1,X2,X4))|v2_struct_0(X1)|~v11_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.38  cnf(c_0_56, negated_conjecture, (v11_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_57, negated_conjecture, (k4_lattices(esk6_0,X1,esk7_0)=k2_lattices(esk6_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_22]), c_0_15])])).
% 0.12/0.38  cnf(c_0_58, negated_conjecture, (k4_lattices(esk6_0,esk7_0,esk9_0)=k2_lattices(esk6_0,esk7_0,esk8_0)), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.38  cnf(c_0_59, negated_conjecture, (k4_lattices(esk6_0,esk9_0,esk9_0)=esk9_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_18]), c_0_48]), c_0_49]), c_0_19]), c_0_15])]), c_0_16])).
% 0.12/0.38  cnf(c_0_60, negated_conjecture, (k1_lattices(esk6_0,k2_lattices(esk6_0,X1,esk9_0),esk9_0)=esk9_0|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_18]), c_0_49]), c_0_15])]), c_0_16])).
% 0.12/0.38  cnf(c_0_61, negated_conjecture, (k1_lattices(esk6_0,esk7_0,esk9_0)=k1_lattices(esk6_0,esk7_0,esk8_0)|~l2_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_29])])).
% 0.12/0.38  cnf(c_0_62, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_63, negated_conjecture, (k4_lattices(esk6_0,X1,esk8_0)=k4_lattices(esk6_0,esk8_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_22]), c_0_15])])).
% 0.12/0.38  cnf(c_0_64, negated_conjecture, (k4_lattices(esk6_0,esk8_0,esk8_0)=esk8_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_23]), c_0_48]), c_0_49]), c_0_19]), c_0_15])]), c_0_16])).
% 0.12/0.38  cnf(c_0_65, negated_conjecture, (k4_lattices(esk6_0,esk8_0,esk9_0)=k2_lattices(esk6_0,esk9_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_54]), c_0_18]), c_0_23])])).
% 0.12/0.38  cnf(c_0_66, negated_conjecture, (k1_lattices(esk6_0,k2_lattices(esk6_0,X1,X2),k2_lattices(esk6_0,X1,esk9_0))=k2_lattices(esk6_0,X1,k1_lattices(esk6_0,X2,esk9_0))|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_18]), c_0_56]), c_0_15])]), c_0_16])).
% 0.12/0.38  cnf(c_0_67, negated_conjecture, (k2_lattices(esk6_0,esk9_0,esk7_0)=k2_lattices(esk6_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_54]), c_0_58]), c_0_18]), c_0_29])])).
% 0.12/0.38  cnf(c_0_68, negated_conjecture, (k2_lattices(esk6_0,esk9_0,esk9_0)=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_28]), c_0_18])])).
% 0.12/0.38  cnf(c_0_69, negated_conjecture, (k1_lattices(esk6_0,k2_lattices(esk6_0,esk7_0,esk8_0),esk9_0)=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_46]), c_0_29])])).
% 0.12/0.38  cnf(c_0_70, negated_conjecture, (k1_lattices(esk6_0,esk7_0,esk9_0)=k1_lattices(esk6_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_15])])).
% 0.12/0.38  cnf(c_0_71, negated_conjecture, (k1_lattices(esk6_0,k2_lattices(esk6_0,X1,X2),k2_lattices(esk6_0,X1,esk8_0))=k2_lattices(esk6_0,X1,k1_lattices(esk6_0,X2,esk8_0))|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_23]), c_0_56]), c_0_15])]), c_0_16])).
% 0.12/0.38  cnf(c_0_72, negated_conjecture, (k2_lattices(esk6_0,esk8_0,esk7_0)=k2_lattices(esk6_0,esk7_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_63]), c_0_34]), c_0_46]), c_0_23]), c_0_29])])).
% 0.12/0.38  cnf(c_0_73, negated_conjecture, (k2_lattices(esk6_0,esk8_0,esk8_0)=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_35]), c_0_23])])).
% 0.12/0.38  cnf(c_0_74, negated_conjecture, (k2_lattices(esk6_0,esk9_0,esk8_0)=k2_lattices(esk6_0,esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_65]), c_0_23])])).
% 0.12/0.38  cnf(c_0_75, negated_conjecture, (k2_lattices(esk6_0,esk9_0,k1_lattices(esk6_0,esk7_0,esk8_0))=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_69]), c_0_70]), c_0_29]), c_0_18])])).
% 0.12/0.38  cnf(c_0_76, negated_conjecture, (k1_lattices(esk6_0,k2_lattices(esk6_0,X1,esk8_0),esk8_0)=esk8_0|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_23]), c_0_49]), c_0_15])]), c_0_16])).
% 0.12/0.38  cnf(c_0_77, negated_conjecture, (k1_lattices(esk6_0,k2_lattices(esk6_0,esk7_0,esk8_0),esk8_0)=k2_lattices(esk6_0,esk8_0,k1_lattices(esk6_0,esk7_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_29]), c_0_23])])).
% 0.12/0.38  cnf(c_0_78, negated_conjecture, (k1_lattices(esk6_0,k2_lattices(esk6_0,esk7_0,esk8_0),k2_lattices(esk6_0,esk8_0,esk9_0))=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_67]), c_0_74]), c_0_75]), c_0_29]), c_0_18])])).
% 0.12/0.38  cnf(c_0_79, negated_conjecture, (k2_lattices(esk6_0,esk8_0,k1_lattices(esk6_0,esk7_0,esk8_0))=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_29])])).
% 0.12/0.38  cnf(c_0_80, negated_conjecture, (esk8_0!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_72]), c_0_70]), c_0_29]), c_0_23])]), c_0_78]), c_0_79]), c_0_80]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 82
% 0.12/0.38  # Proof object clause steps            : 63
% 0.12/0.38  # Proof object formula steps           : 19
% 0.12/0.38  # Proof object conjectures             : 54
% 0.12/0.38  # Proof object clause conjectures      : 51
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 22
% 0.12/0.38  # Proof object initial formulas used   : 9
% 0.12/0.38  # Proof object generating inferences   : 39
% 0.12/0.38  # Proof object simplifying inferences  : 127
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 9
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 32
% 0.12/0.38  # Removed in clause preprocessing      : 1
% 0.12/0.38  # Initial clauses in saturation        : 31
% 0.12/0.38  # Processed clauses                    : 155
% 0.12/0.38  # ...of these trivial                  : 1
% 0.12/0.38  # ...subsumed                          : 6
% 0.12/0.38  # ...remaining for further processing  : 147
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 6
% 0.12/0.38  # Backward-rewritten                   : 8
% 0.12/0.38  # Generated clauses                    : 200
% 0.12/0.38  # ...of the previous two non-trivial   : 151
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 200
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 102
% 0.12/0.38  #    Positive orientable unit clauses  : 51
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 2
% 0.12/0.38  #    Non-unit-clauses                  : 49
% 0.12/0.38  # Current number of unprocessed clauses: 58
% 0.12/0.38  # ...number of literals in the above   : 138
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 45
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 686
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 348
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 12
% 0.12/0.38  # Unit Clause-clause subsumption calls : 73
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 114
% 0.12/0.38  # BW rewrite match successes           : 6
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 8657
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.038 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.042 s
% 0.12/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
