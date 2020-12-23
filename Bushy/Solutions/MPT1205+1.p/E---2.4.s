%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattices__t39_lattices.p : TPTP v0.0.0. Released v0.0.0.
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
% Statistics : Number of formulae       :   38 ( 145 expanded)
%              Number of clauses        :   23 (  50 expanded)
%              Number of leaves         :    7 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  191 ( 699 expanded)
%              Number of equality atoms :   28 (  94 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k3_lattices(X1,k5_lattices(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t39_lattices.p',t39_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t39_lattices.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/lattices__t39_lattices.p',d16_lattices)).

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t39_lattices.p',dt_k5_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/lattices__t39_lattices.p',cc1_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/lattices__t39_lattices.p',d8_lattices)).

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t39_lattices.p',redefinition_k3_lattices)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v13_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => k3_lattices(X1,k5_lattices(X1),X2) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t39_lattices])).

fof(c_0_8,plain,(
    ! [X43] :
      ( ( l1_lattices(X43)
        | ~ l3_lattices(X43) )
      & ( l2_lattices(X43)
        | ~ l3_lattices(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v13_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & k3_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X15,X16,X17] :
      ( ( k2_lattices(X15,X16,X17) = X16
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | X16 != k5_lattices(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v13_lattices(X15)
        | v2_struct_0(X15)
        | ~ l1_lattices(X15) )
      & ( k2_lattices(X15,X17,X16) = X16
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | X16 != k5_lattices(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v13_lattices(X15)
        | v2_struct_0(X15)
        | ~ l1_lattices(X15) )
      & ( m1_subset_1(esk3_2(X15,X16),u1_struct_0(X15))
        | X16 = k5_lattices(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v13_lattices(X15)
        | v2_struct_0(X15)
        | ~ l1_lattices(X15) )
      & ( k2_lattices(X15,X16,esk3_2(X15,X16)) != X16
        | k2_lattices(X15,esk3_2(X15,X16),X16) != X16
        | X16 = k5_lattices(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v13_lattices(X15)
        | v2_struct_0(X15)
        | ~ l1_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

cnf(c_0_11,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X40] :
      ( v2_struct_0(X40)
      | ~ l1_lattices(X40)
      | m1_subset_1(k5_lattices(X40),u1_struct_0(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

cnf(c_0_14,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | X2 != k5_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v13_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( l1_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
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

fof(c_0_21,plain,(
    ! [X19,X20,X21] :
      ( ( ~ v8_lattices(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | k1_lattices(X19,k2_lattices(X19,X20,X21),X21) = X21
        | v2_struct_0(X19)
        | ~ l3_lattices(X19) )
      & ( m1_subset_1(esk4_1(X19),u1_struct_0(X19))
        | v8_lattices(X19)
        | v2_struct_0(X19)
        | ~ l3_lattices(X19) )
      & ( m1_subset_1(esk5_1(X19),u1_struct_0(X19))
        | v8_lattices(X19)
        | v2_struct_0(X19)
        | ~ l3_lattices(X19) )
      & ( k1_lattices(X19,k2_lattices(X19,esk4_1(X19),esk5_1(X19)),esk5_1(X19)) != esk5_1(X19)
        | v8_lattices(X19)
        | v2_struct_0(X19)
        | ~ l3_lattices(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).

cnf(c_0_22,negated_conjecture,
    ( k2_lattices(esk1_0,X1,esk2_0) = X1
    | X1 != k5_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])]),c_0_17]),c_0_18])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_18]),c_0_17])).

cnf(c_0_24,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_26,plain,(
    ! [X52,X53,X54] :
      ( v2_struct_0(X52)
      | ~ v4_lattices(X52)
      | ~ l2_lattices(X52)
      | ~ m1_subset_1(X53,u1_struct_0(X52))
      | ~ m1_subset_1(X54,u1_struct_0(X52))
      | k3_lattices(X52,X53,X54) = k1_lattices(X52,X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

cnf(c_0_27,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k2_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) = k5_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_12]),c_0_25])]),c_0_17])).

cnf(c_0_30,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k1_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_15]),c_0_23]),c_0_12])]),c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( v4_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_12]),c_0_25])]),c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( k3_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( ~ l2_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_15]),c_0_23])]),c_0_34]),c_0_17])).

cnf(c_0_36,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_12])]),
    [proof]).
%------------------------------------------------------------------------------
