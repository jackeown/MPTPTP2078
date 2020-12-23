%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:24 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 240 expanded)
%              Number of clauses        :   37 (  85 expanded)
%              Number of leaves         :    9 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  262 (1168 expanded)
%              Number of equality atoms :   39 ( 147 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(t39_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k3_lattices(X1,k5_lattices(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_lattices)).

fof(d16_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v13_lattices(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( X2 = k5_lattices(X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( k2_lattices(X1,X2,X3) = X2
                    & k2_lattices(X1,X3,X2) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).

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

fof(c_0_9,plain,(
    ! [X12] :
      ( v2_struct_0(X12)
      | ~ l1_lattices(X12)
      | m1_subset_1(k5_lattices(X12),u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_10,plain,(
    ! [X13] :
      ( ( l1_lattices(X13)
        | ~ l3_lattices(X13) )
      & ( l2_lattices(X13)
        | ~ l3_lattices(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v13_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => k3_lattices(X1,k5_lattices(X1),X2) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t39_lattices])).

fof(c_0_12,plain,(
    ! [X5,X6,X7] :
      ( ( k2_lattices(X5,X6,X7) = X6
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | X6 != k5_lattices(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v13_lattices(X5)
        | v2_struct_0(X5)
        | ~ l1_lattices(X5) )
      & ( k2_lattices(X5,X7,X6) = X6
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | X6 != k5_lattices(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v13_lattices(X5)
        | v2_struct_0(X5)
        | ~ l1_lattices(X5) )
      & ( m1_subset_1(esk1_2(X5,X6),u1_struct_0(X5))
        | X6 = k5_lattices(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v13_lattices(X5)
        | v2_struct_0(X5)
        | ~ l1_lattices(X5) )
      & ( k2_lattices(X5,X6,esk1_2(X5,X6)) != X6
        | k2_lattices(X5,esk1_2(X5,X6),X6) != X6
        | X6 = k5_lattices(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v13_lattices(X5)
        | v2_struct_0(X5)
        | ~ l1_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v10_lattices(esk2_0)
    & v13_lattices(esk2_0)
    & l3_lattices(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & k3_lattices(esk2_0,k5_lattices(esk2_0),esk3_0) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

cnf(c_0_16,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X17,X18,X19] :
      ( v2_struct_0(X17)
      | ~ v6_lattices(X17)
      | ~ l1_lattices(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | k4_lattices(X17,X18,X19) = k2_lattices(X17,X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

cnf(c_0_18,plain,
    ( m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v13_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk2_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k2_lattices(esk2_0,esk3_0,k5_lattices(esk2_0)) = k5_lattices(esk2_0)
    | ~ l1_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k4_lattices(esk2_0,X1,k5_lattices(esk2_0)) = k2_lattices(esk2_0,X1,k5_lattices(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ l1_lattices(esk2_0)
    | ~ v6_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( k2_lattices(esk2_0,esk3_0,k5_lattices(esk2_0)) = k5_lattices(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_14]),c_0_19])])).

fof(c_0_29,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ v4_lattices(X14)
      | ~ l2_lattices(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | k3_lattices(X14,X15,X16) = k1_lattices(X14,X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

fof(c_0_30,plain,(
    ! [X20,X21,X22] :
      ( v2_struct_0(X20)
      | ~ v6_lattices(X20)
      | ~ v8_lattices(X20)
      | ~ l3_lattices(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | ~ m1_subset_1(X22,u1_struct_0(X20))
      | r1_lattices(X20,k4_lattices(X20,X21,X22),X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_lattices])])])])).

cnf(c_0_31,negated_conjecture,
    ( k4_lattices(esk2_0,esk3_0,k5_lattices(esk2_0)) = k5_lattices(esk2_0)
    | ~ l1_lattices(esk2_0)
    | ~ v6_lattices(esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_22]),c_0_28])).

fof(c_0_32,plain,(
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

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,k4_lattices(X1,X2,X3),X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k4_lattices(esk2_0,esk3_0,k5_lattices(esk2_0)) = k5_lattices(esk2_0)
    | ~ v6_lattices(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_14]),c_0_19])])).

cnf(c_0_36,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( k3_lattices(esk2_0,X1,esk3_0) = k1_lattices(esk2_0,X1,esk3_0)
    | ~ l2_lattices(esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ v4_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_22]),c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( r1_lattices(esk2_0,k4_lattices(esk2_0,X1,k5_lattices(esk2_0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ v8_lattices(esk2_0)
    | ~ v6_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_25]),c_0_19])]),c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( k4_lattices(esk2_0,esk3_0,k5_lattices(esk2_0)) = k5_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_19])]),c_0_20])).

cnf(c_0_41,negated_conjecture,
    ( k3_lattices(esk2_0,k5_lattices(esk2_0),esk3_0) = k1_lattices(esk2_0,k5_lattices(esk2_0),esk3_0)
    | ~ l2_lattices(esk2_0)
    | ~ v4_lattices(esk2_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_25])).

cnf(c_0_42,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_43,negated_conjecture,
    ( r1_lattices(esk2_0,k5_lattices(esk2_0),esk3_0)
    | ~ v8_lattices(esk2_0)
    | ~ v6_lattices(esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_22]),c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( k3_lattices(esk2_0,k5_lattices(esk2_0),esk3_0) = k1_lattices(esk2_0,k5_lattices(esk2_0),esk3_0)
    | ~ v4_lattices(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_19])])).

cnf(c_0_45,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_46,plain,(
    ! [X9,X10,X11] :
      ( ( ~ r1_lattices(X9,X10,X11)
        | k1_lattices(X9,X10,X11) = X11
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l2_lattices(X9) )
      & ( k1_lattices(X9,X10,X11) != X11
        | r1_lattices(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l2_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

cnf(c_0_47,negated_conjecture,
    ( r1_lattices(esk2_0,k5_lattices(esk2_0),esk3_0)
    | ~ v8_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_36]),c_0_37]),c_0_19])]),c_0_20])).

cnf(c_0_48,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( k3_lattices(esk2_0,k5_lattices(esk2_0),esk3_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( k3_lattices(esk2_0,k5_lattices(esk2_0),esk3_0) = k1_lattices(esk2_0,k5_lattices(esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_37]),c_0_19])]),c_0_20])).

cnf(c_0_51,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r1_lattices(esk2_0,k5_lattices(esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_37]),c_0_19])]),c_0_20])).

cnf(c_0_53,negated_conjecture,
    ( k1_lattices(esk2_0,k5_lattices(esk2_0),esk3_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( ~ l2_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_22]),c_0_25])]),c_0_53]),c_0_20])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_42]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.19/0.38  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.029 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.19/0.38  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.19/0.38  fof(t39_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k3_lattices(X1,k5_lattices(X1),X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_lattices)).
% 0.19/0.38  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 0.19/0.38  fof(redefinition_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 0.19/0.38  fof(redefinition_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 0.19/0.38  fof(t23_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>r1_lattices(X1,k4_lattices(X1,X2,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_lattices)).
% 0.19/0.38  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.19/0.38  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 0.19/0.38  fof(c_0_9, plain, ![X12]:(v2_struct_0(X12)|~l1_lattices(X12)|m1_subset_1(k5_lattices(X12),u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.19/0.38  fof(c_0_10, plain, ![X13]:((l1_lattices(X13)|~l3_lattices(X13))&(l2_lattices(X13)|~l3_lattices(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.19/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k3_lattices(X1,k5_lattices(X1),X2)=X2))), inference(assume_negation,[status(cth)],[t39_lattices])).
% 0.19/0.38  fof(c_0_12, plain, ![X5, X6, X7]:(((k2_lattices(X5,X6,X7)=X6|~m1_subset_1(X7,u1_struct_0(X5))|X6!=k5_lattices(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~v13_lattices(X5)|(v2_struct_0(X5)|~l1_lattices(X5)))&(k2_lattices(X5,X7,X6)=X6|~m1_subset_1(X7,u1_struct_0(X5))|X6!=k5_lattices(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~v13_lattices(X5)|(v2_struct_0(X5)|~l1_lattices(X5))))&((m1_subset_1(esk1_2(X5,X6),u1_struct_0(X5))|X6=k5_lattices(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~v13_lattices(X5)|(v2_struct_0(X5)|~l1_lattices(X5)))&(k2_lattices(X5,X6,esk1_2(X5,X6))!=X6|k2_lattices(X5,esk1_2(X5,X6),X6)!=X6|X6=k5_lattices(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~v13_lattices(X5)|(v2_struct_0(X5)|~l1_lattices(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.19/0.38  cnf(c_0_13, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_14, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk2_0)&v10_lattices(esk2_0))&v13_lattices(esk2_0))&l3_lattices(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&k3_lattices(esk2_0,k5_lattices(esk2_0),esk3_0)!=esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.19/0.38  cnf(c_0_16, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  fof(c_0_17, plain, ![X17, X18, X19]:(v2_struct_0(X17)|~v6_lattices(X17)|~l1_lattices(X17)|~m1_subset_1(X18,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|k4_lattices(X17,X18,X19)=k2_lattices(X17,X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).
% 0.19/0.38  cnf(c_0_18, plain, (m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (l3_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_21, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]), c_0_13])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (v13_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_24, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(k5_lattices(esk2_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (k2_lattices(esk2_0,esk3_0,k5_lattices(esk2_0))=k5_lattices(esk2_0)|~l1_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])]), c_0_20])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (k4_lattices(esk2_0,X1,k5_lattices(esk2_0))=k2_lattices(esk2_0,X1,k5_lattices(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~l1_lattices(esk2_0)|~v6_lattices(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_20])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (k2_lattices(esk2_0,esk3_0,k5_lattices(esk2_0))=k5_lattices(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_14]), c_0_19])])).
% 0.19/0.38  fof(c_0_29, plain, ![X14, X15, X16]:(v2_struct_0(X14)|~v4_lattices(X14)|~l2_lattices(X14)|~m1_subset_1(X15,u1_struct_0(X14))|~m1_subset_1(X16,u1_struct_0(X14))|k3_lattices(X14,X15,X16)=k1_lattices(X14,X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).
% 0.19/0.38  fof(c_0_30, plain, ![X20, X21, X22]:(v2_struct_0(X20)|~v6_lattices(X20)|~v8_lattices(X20)|~l3_lattices(X20)|(~m1_subset_1(X21,u1_struct_0(X20))|(~m1_subset_1(X22,u1_struct_0(X20))|r1_lattices(X20,k4_lattices(X20,X21,X22),X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_lattices])])])])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (k4_lattices(esk2_0,esk3_0,k5_lattices(esk2_0))=k5_lattices(esk2_0)|~l1_lattices(esk2_0)|~v6_lattices(esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_22]), c_0_28])).
% 0.19/0.38  fof(c_0_32, plain, ![X4]:(((((((~v2_struct_0(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))&(v4_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v5_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v6_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v7_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v8_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v9_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.19/0.38  cnf(c_0_33, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_34, plain, (v2_struct_0(X1)|r1_lattices(X1,k4_lattices(X1,X2,X3),X2)|~v6_lattices(X1)|~v8_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (k4_lattices(esk2_0,esk3_0,k5_lattices(esk2_0))=k5_lattices(esk2_0)|~v6_lattices(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_14]), c_0_19])])).
% 0.19/0.38  cnf(c_0_36, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (v10_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (k3_lattices(esk2_0,X1,esk3_0)=k1_lattices(esk2_0,X1,esk3_0)|~l2_lattices(esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~v4_lattices(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_22]), c_0_20])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (r1_lattices(esk2_0,k4_lattices(esk2_0,X1,k5_lattices(esk2_0)),X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~v8_lattices(esk2_0)|~v6_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_25]), c_0_19])]), c_0_20])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (k4_lattices(esk2_0,esk3_0,k5_lattices(esk2_0))=k5_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_19])]), c_0_20])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (k3_lattices(esk2_0,k5_lattices(esk2_0),esk3_0)=k1_lattices(esk2_0,k5_lattices(esk2_0),esk3_0)|~l2_lattices(esk2_0)|~v4_lattices(esk2_0)), inference(spm,[status(thm)],[c_0_38, c_0_25])).
% 0.19/0.38  cnf(c_0_42, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (r1_lattices(esk2_0,k5_lattices(esk2_0),esk3_0)|~v8_lattices(esk2_0)|~v6_lattices(esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_22]), c_0_40])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (k3_lattices(esk2_0,k5_lattices(esk2_0),esk3_0)=k1_lattices(esk2_0,k5_lattices(esk2_0),esk3_0)|~v4_lattices(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_19])])).
% 0.19/0.38  cnf(c_0_45, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  fof(c_0_46, plain, ![X9, X10, X11]:((~r1_lattices(X9,X10,X11)|k1_lattices(X9,X10,X11)=X11|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l2_lattices(X9)))&(k1_lattices(X9,X10,X11)!=X11|r1_lattices(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l2_lattices(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (r1_lattices(esk2_0,k5_lattices(esk2_0),esk3_0)|~v8_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_36]), c_0_37]), c_0_19])]), c_0_20])).
% 0.19/0.38  cnf(c_0_48, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (k3_lattices(esk2_0,k5_lattices(esk2_0),esk3_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (k3_lattices(esk2_0,k5_lattices(esk2_0),esk3_0)=k1_lattices(esk2_0,k5_lattices(esk2_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_37]), c_0_19])]), c_0_20])).
% 0.19/0.38  cnf(c_0_51, plain, (k1_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (r1_lattices(esk2_0,k5_lattices(esk2_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_37]), c_0_19])]), c_0_20])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (k1_lattices(esk2_0,k5_lattices(esk2_0),esk3_0)!=esk3_0), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (~l2_lattices(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_22]), c_0_25])]), c_0_53]), c_0_20])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_42]), c_0_19])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 56
% 0.19/0.38  # Proof object clause steps            : 37
% 0.19/0.38  # Proof object formula steps           : 19
% 0.19/0.38  # Proof object conjectures             : 27
% 0.19/0.38  # Proof object clause conjectures      : 24
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 17
% 0.19/0.38  # Proof object initial formulas used   : 9
% 0.19/0.38  # Proof object generating inferences   : 18
% 0.19/0.38  # Proof object simplifying inferences  : 43
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 9
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 25
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 24
% 0.19/0.38  # Processed clauses                    : 112
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 0
% 0.19/0.38  # ...remaining for further processing  : 112
% 0.19/0.38  # Other redundant clauses eliminated   : 2
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 15
% 0.19/0.38  # Backward-rewritten                   : 18
% 0.19/0.38  # Generated clauses                    : 87
% 0.19/0.38  # ...of the previous two non-trivial   : 86
% 0.19/0.38  # Contextual simplify-reflections      : 2
% 0.19/0.38  # Paramodulations                      : 85
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 2
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 53
% 0.19/0.38  #    Positive orientable unit clauses  : 20
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 3
% 0.19/0.38  #    Non-unit-clauses                  : 30
% 0.19/0.38  # Current number of unprocessed clauses: 22
% 0.19/0.38  # ...number of literals in the above   : 102
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 57
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 460
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 196
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 17
% 0.19/0.38  # Unit Clause-clause subsumption calls : 44
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 23
% 0.19/0.38  # BW rewrite match successes           : 15
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 4396
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.035 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.038 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
