%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1496+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:05 EST 2020

% Result     : Theorem 9.26s
% Output     : CNFRefutation 9.26s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 414 expanded)
%              Number of clauses        :   20 ( 129 expanded)
%              Number of leaves         :    5 ( 102 expanded)
%              Depth                    :   10
%              Number of atoms          :  115 (2078 expanded)
%              Number of equality atoms :    8 (  48 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_lattice3,conjecture,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & l3_lattices(X2) )
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(k3_lattice3(X2)))
         => ( r1_lattice3(k3_lattice3(X2),X1,X3)
          <=> r3_lattice3(X2,k5_lattice3(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_lattice3)).

fof(d4_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
         => k5_lattice3(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_lattice3)).

fof(dt_k5_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
     => m1_subset_1(k5_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattice3)).

fof(d3_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattice3(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattice3)).

fof(t28_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & l3_lattices(X2) )
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(X2))
         => ( r3_lattice3(X2,X3,X1)
          <=> r1_lattice3(k3_lattice3(X2),X1,k4_lattice3(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_lattice3)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( ~ v2_struct_0(X2)
          & v10_lattices(X2)
          & l3_lattices(X2) )
       => ! [X3] :
            ( m1_subset_1(X3,u1_struct_0(k3_lattice3(X2)))
           => ( r1_lattice3(k3_lattice3(X2),X1,X3)
            <=> r3_lattice3(X2,k5_lattice3(X2,X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_lattice3])).

fof(c_0_6,plain,(
    ! [X8925,X8926] :
      ( v2_struct_0(X8925)
      | ~ v10_lattices(X8925)
      | ~ l3_lattices(X8925)
      | ~ m1_subset_1(X8926,u1_struct_0(k3_lattice3(X8925)))
      | k5_lattice3(X8925,X8926) = X8926 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_lattice3])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk1027_0)
    & v10_lattices(esk1027_0)
    & l3_lattices(esk1027_0)
    & m1_subset_1(esk1028_0,u1_struct_0(k3_lattice3(esk1027_0)))
    & ( ~ r1_lattice3(k3_lattice3(esk1027_0),esk1026_0,esk1028_0)
      | ~ r3_lattice3(esk1027_0,k5_lattice3(esk1027_0,esk1028_0),esk1026_0) )
    & ( r1_lattice3(k3_lattice3(esk1027_0),esk1026_0,esk1028_0)
      | r3_lattice3(esk1027_0,k5_lattice3(esk1027_0,esk1028_0),esk1026_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X8969,X8970] :
      ( v2_struct_0(X8969)
      | ~ v10_lattices(X8969)
      | ~ l3_lattices(X8969)
      | ~ m1_subset_1(X8970,u1_struct_0(k3_lattice3(X8969)))
      | m1_subset_1(k5_lattice3(X8969,X8970),u1_struct_0(X8969)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattice3])])])).

cnf(c_0_9,plain,
    ( v2_struct_0(X1)
    | k5_lattice3(X1,X2) = X2
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk1028_0,u1_struct_0(k3_lattice3(esk1027_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( l3_lattices(esk1027_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v10_lattices(esk1027_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1027_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_14,plain,(
    ! [X8923,X8924] :
      ( v2_struct_0(X8923)
      | ~ v10_lattices(X8923)
      | ~ l3_lattices(X8923)
      | ~ m1_subset_1(X8924,u1_struct_0(X8923))
      | k4_lattice3(X8923,X8924) = X8924 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattice3])])])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattice3(X1,X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( k5_lattice3(esk1027_0,esk1028_0) = esk1028_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

fof(c_0_17,plain,(
    ! [X9162,X9163,X9164] :
      ( ( ~ r3_lattice3(X9163,X9164,X9162)
        | r1_lattice3(k3_lattice3(X9163),X9162,k4_lattice3(X9163,X9164))
        | ~ m1_subset_1(X9164,u1_struct_0(X9163))
        | v2_struct_0(X9163)
        | ~ v10_lattices(X9163)
        | ~ l3_lattices(X9163) )
      & ( ~ r1_lattice3(k3_lattice3(X9163),X9162,k4_lattice3(X9163,X9164))
        | r3_lattice3(X9163,X9164,X9162)
        | ~ m1_subset_1(X9164,u1_struct_0(X9163))
        | v2_struct_0(X9163)
        | ~ v10_lattices(X9163)
        | ~ l3_lattices(X9163) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t28_lattice3])])])])])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | k4_lattice3(X1,X2) = X2
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk1028_0,u1_struct_0(esk1027_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_10]),c_0_16]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_20,plain,
    ( r3_lattice3(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ r1_lattice3(k3_lattice3(X1),X2,k4_lattice3(X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( k4_lattice3(esk1027_0,esk1028_0) = esk1028_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( r1_lattice3(k3_lattice3(esk1027_0),esk1026_0,esk1028_0)
    | r3_lattice3(esk1027_0,k5_lattice3(esk1027_0,esk1028_0),esk1026_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_lattice3(k3_lattice3(esk1027_0),esk1026_0,esk1028_0)
    | ~ r3_lattice3(esk1027_0,k5_lattice3(esk1027_0,esk1028_0),esk1026_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( r3_lattice3(esk1027_0,esk1028_0,X1)
    | ~ r1_lattice3(k3_lattice3(esk1027_0),X1,esk1028_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_11]),c_0_12]),c_0_19])]),c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( r1_lattice3(k3_lattice3(esk1027_0),esk1026_0,esk1028_0)
    | r3_lattice3(esk1027_0,esk1028_0,esk1026_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_lattice3(k3_lattice3(esk1027_0),esk1026_0,esk1028_0)
    | ~ r3_lattice3(esk1027_0,esk1028_0,esk1026_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( r3_lattice3(esk1027_0,esk1028_0,esk1026_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,plain,
    ( r1_lattice3(k3_lattice3(X1),X3,k4_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_lattice3(k3_lattice3(esk1027_0),esk1026_0,esk1028_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_27]),c_0_21]),c_0_11]),c_0_12]),c_0_19])]),c_0_29]),c_0_13]),
    [proof]).
%------------------------------------------------------------------------------
