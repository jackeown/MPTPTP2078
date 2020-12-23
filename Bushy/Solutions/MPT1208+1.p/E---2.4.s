%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattices__t43_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:02 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 347 expanded)
%              Number of clauses        :   34 ( 121 expanded)
%              Number of leaves         :   10 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  261 (1653 expanded)
%              Number of equality atoms :   43 ( 205 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v14_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattices(X1,k6_lattices(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',t43_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',cc1_lattices)).

fof(dt_k6_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => m1_subset_1(k6_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',dt_k6_lattices)).

fof(d17_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ( v14_lattices(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( X2 = k6_lattices(X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( k1_lattices(X1,X2,X3) = X2
                    & k1_lattices(X1,X3,X2) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',d17_lattices)).

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',redefinition_k3_lattices)).

fof(commutativity_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',commutativity_k3_lattices)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',commutativity_k4_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',d9_lattices)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t43_lattices.p',redefinition_k4_lattices)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v14_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => k4_lattices(X1,k6_lattices(X1),X2) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t43_lattices])).

fof(c_0_11,plain,(
    ! [X43] :
      ( ( l1_lattices(X43)
        | ~ l3_lattices(X43) )
      & ( l2_lattices(X43)
        | ~ l3_lattices(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v14_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & k4_lattices(esk1_0,k6_lattices(esk1_0),esk2_0) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X79] :
      ( ( ~ v2_struct_0(X79)
        | v2_struct_0(X79)
        | ~ v10_lattices(X79)
        | ~ l3_lattices(X79) )
      & ( v4_lattices(X79)
        | v2_struct_0(X79)
        | ~ v10_lattices(X79)
        | ~ l3_lattices(X79) )
      & ( v5_lattices(X79)
        | v2_struct_0(X79)
        | ~ v10_lattices(X79)
        | ~ l3_lattices(X79) )
      & ( v6_lattices(X79)
        | v2_struct_0(X79)
        | ~ v10_lattices(X79)
        | ~ l3_lattices(X79) )
      & ( v7_lattices(X79)
        | v2_struct_0(X79)
        | ~ v10_lattices(X79)
        | ~ l3_lattices(X79) )
      & ( v8_lattices(X79)
        | v2_struct_0(X79)
        | ~ v10_lattices(X79)
        | ~ l3_lattices(X79) )
      & ( v9_lattices(X79)
        | v2_struct_0(X79)
        | ~ v10_lattices(X79)
        | ~ l3_lattices(X79) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_14,plain,(
    ! [X40] :
      ( v2_struct_0(X40)
      | ~ l2_lattices(X40)
      | m1_subset_1(k6_lattices(X40),u1_struct_0(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_lattices])])])).

cnf(c_0_15,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X15,X16,X17] :
      ( ( k1_lattices(X15,X16,X17) = X16
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | X16 != k6_lattices(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v14_lattices(X15)
        | v2_struct_0(X15)
        | ~ l2_lattices(X15) )
      & ( k1_lattices(X15,X17,X16) = X16
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | X16 != k6_lattices(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v14_lattices(X15)
        | v2_struct_0(X15)
        | ~ l2_lattices(X15) )
      & ( m1_subset_1(esk3_2(X15,X16),u1_struct_0(X15))
        | X16 = k6_lattices(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v14_lattices(X15)
        | v2_struct_0(X15)
        | ~ l2_lattices(X15) )
      & ( k1_lattices(X15,X16,esk3_2(X15,X16)) != X16
        | k1_lattices(X15,esk3_2(X15,X16),X16) != X16
        | X16 = k6_lattices(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v14_lattices(X15)
        | v2_struct_0(X15)
        | ~ l2_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattices])])])])])])).

fof(c_0_18,plain,(
    ! [X52,X53,X54] :
      ( v2_struct_0(X52)
      | ~ v4_lattices(X52)
      | ~ l2_lattices(X52)
      | ~ m1_subset_1(X53,u1_struct_0(X52))
      | ~ m1_subset_1(X54,u1_struct_0(X52))
      | k3_lattices(X52,X53,X54) = k1_lattices(X52,X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

cnf(c_0_19,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_22,plain,(
    ! [X9,X10,X11] :
      ( v2_struct_0(X9)
      | ~ v4_lattices(X9)
      | ~ l2_lattices(X9)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | k3_lattices(X9,X10,X11) = k3_lattices(X9,X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( l2_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_25,plain,
    ( k1_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | X2 != k6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v14_lattices(X1)
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( v14_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( v4_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_16]),c_0_20])]),c_0_21])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k6_lattices(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( k1_lattices(esk1_0,X1,esk2_0) = X1
    | X1 != k6_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])]),c_0_21]),c_0_24])])).

cnf(c_0_33,negated_conjecture,
    ( k3_lattices(esk1_0,X1,esk2_0) = k1_lattices(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_26]),c_0_21]),c_0_24]),c_0_29])])).

cnf(c_0_34,negated_conjecture,
    ( k3_lattices(esk1_0,X1,k6_lattices(esk1_0)) = k3_lattices(esk1_0,k6_lattices(esk1_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_24]),c_0_29])]),c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( k1_lattices(esk1_0,k6_lattices(esk1_0),esk2_0) = k6_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

fof(c_0_36,plain,(
    ! [X12,X13,X14] :
      ( v2_struct_0(X12)
      | ~ v6_lattices(X12)
      | ~ l1_lattices(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | k4_lattices(X12,X13,X14) = k4_lattices(X12,X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_37,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_38,plain,(
    ! [X19,X20,X21] :
      ( ( ~ v9_lattices(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | k2_lattices(X19,X20,k1_lattices(X19,X20,X21)) = X20
        | v2_struct_0(X19)
        | ~ l3_lattices(X19) )
      & ( m1_subset_1(esk4_1(X19),u1_struct_0(X19))
        | v9_lattices(X19)
        | v2_struct_0(X19)
        | ~ l3_lattices(X19) )
      & ( m1_subset_1(esk5_1(X19),u1_struct_0(X19))
        | v9_lattices(X19)
        | v2_struct_0(X19)
        | ~ l3_lattices(X19) )
      & ( k2_lattices(X19,esk4_1(X19),k1_lattices(X19,esk4_1(X19),esk5_1(X19))) != esk4_1(X19)
        | v9_lattices(X19)
        | v2_struct_0(X19)
        | ~ l3_lattices(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).

cnf(c_0_39,negated_conjecture,
    ( k3_lattices(esk1_0,esk2_0,k6_lattices(esk1_0)) = k6_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_31]),c_0_26])])).

cnf(c_0_40,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_16]),c_0_20])]),c_0_21])).

fof(c_0_43,plain,(
    ! [X59,X60,X61] :
      ( v2_struct_0(X59)
      | ~ v6_lattices(X59)
      | ~ l1_lattices(X59)
      | ~ m1_subset_1(X60,u1_struct_0(X59))
      | ~ m1_subset_1(X61,u1_struct_0(X59))
      | k4_lattices(X59,X60,X61) = k2_lattices(X59,X60,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

cnf(c_0_44,plain,
    ( k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,k6_lattices(esk1_0)) = k6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_39]),c_0_24]),c_0_29]),c_0_31]),c_0_26])]),c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_16]),c_0_20])]),c_0_21])).

cnf(c_0_47,negated_conjecture,
    ( k4_lattices(esk1_0,k6_lattices(esk1_0),esk2_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_48,negated_conjecture,
    ( k4_lattices(esk1_0,X1,k6_lattices(esk1_0)) = k4_lattices(esk1_0,k6_lattices(esk1_0),X1)
    | ~ l1_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_31]),c_0_42])]),c_0_21])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k2_lattices(esk1_0,esk2_0,k6_lattices(esk1_0)) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_31]),c_0_26]),c_0_16])]),c_0_21])).

cnf(c_0_51,negated_conjecture,
    ( k4_lattices(esk1_0,esk2_0,k6_lattices(esk1_0)) != esk2_0
    | ~ l1_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_26])])).

cnf(c_0_52,negated_conjecture,
    ( ~ l1_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_42]),c_0_31]),c_0_26])]),c_0_21]),c_0_51])).

cnf(c_0_53,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
