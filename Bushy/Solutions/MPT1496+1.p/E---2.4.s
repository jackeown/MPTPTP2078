%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattice3__t29_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:54 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 415 expanded)
%              Number of clauses        :   21 ( 130 expanded)
%              Number of leaves         :    5 ( 102 expanded)
%              Depth                    :   10
%              Number of atoms          :  117 (2080 expanded)
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
    file('/export/starexec/sandbox2/benchmark/lattice3__t29_lattice3.p',t29_lattice3)).

fof(d4_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
         => k5_lattice3(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t29_lattice3.p',d4_lattice3)).

fof(dt_k5_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
     => m1_subset_1(k5_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t29_lattice3.p',dt_k5_lattice3)).

fof(d3_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattice3(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t29_lattice3.p',d3_lattice3)).

fof(t28_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & l3_lattices(X2) )
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(X2))
         => ( r3_lattice3(X2,X3,X1)
          <=> r1_lattice3(k3_lattice3(X2),X1,k4_lattice3(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t29_lattice3.p',t28_lattice3)).

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
    ! [X13,X14] :
      ( v2_struct_0(X13)
      | ~ v10_lattices(X13)
      | ~ l3_lattices(X13)
      | ~ m1_subset_1(X14,u1_struct_0(k3_lattice3(X13)))
      | k5_lattice3(X13,X14) = X14 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_lattice3])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v10_lattices(esk2_0)
    & l3_lattices(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(k3_lattice3(esk2_0)))
    & ( ~ r1_lattice3(k3_lattice3(esk2_0),esk1_0,esk3_0)
      | ~ r3_lattice3(esk2_0,k5_lattice3(esk2_0,esk3_0),esk1_0) )
    & ( r1_lattice3(k3_lattice3(esk2_0),esk1_0,esk3_0)
      | r3_lattice3(esk2_0,k5_lattice3(esk2_0,esk3_0),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X21,X22] :
      ( v2_struct_0(X21)
      | ~ v10_lattices(X21)
      | ~ l3_lattices(X21)
      | ~ m1_subset_1(X22,u1_struct_0(k3_lattice3(X21)))
      | m1_subset_1(k5_lattice3(X21,X22),u1_struct_0(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattice3])])])).

cnf(c_0_9,plain,
    ( v2_struct_0(X1)
    | k5_lattice3(X1,X2) = X2
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k3_lattice3(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_14,plain,(
    ! [X11,X12] :
      ( v2_struct_0(X11)
      | ~ v10_lattices(X11)
      | ~ l3_lattices(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | k4_lattice3(X11,X12) = X12 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattice3])])])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattice3(X1,X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( k5_lattice3(esk2_0,esk3_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

fof(c_0_17,plain,(
    ! [X43,X44,X45] :
      ( ( ~ r3_lattice3(X44,X45,X43)
        | r1_lattice3(k3_lattice3(X44),X43,k4_lattice3(X44,X45))
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ v10_lattices(X44)
        | ~ l3_lattices(X44) )
      & ( ~ r1_lattice3(k3_lattice3(X44),X43,k4_lattice3(X44,X45))
        | r3_lattice3(X44,X45,X43)
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ v10_lattices(X44)
        | ~ l3_lattices(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t28_lattice3])])])])])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | k4_lattice3(X1,X2) = X2
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_20,plain,
    ( r3_lattice3(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ r1_lattice3(k3_lattice3(X1),X2,k4_lattice3(X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( k4_lattice3(esk2_0,esk3_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( r1_lattice3(k3_lattice3(esk2_0),esk1_0,esk3_0)
    | r3_lattice3(esk2_0,k5_lattice3(esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_lattice3(k3_lattice3(esk2_0),esk1_0,esk3_0)
    | ~ r3_lattice3(esk2_0,k5_lattice3(esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( r3_lattice3(esk2_0,esk3_0,X1)
    | ~ r1_lattice3(k3_lattice3(esk2_0),X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_19]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( r3_lattice3(esk2_0,esk3_0,esk1_0)
    | r1_lattice3(k3_lattice3(esk2_0),esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( ~ r3_lattice3(esk2_0,esk3_0,esk1_0)
    | ~ r1_lattice3(k3_lattice3(esk2_0),esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( r3_lattice3(esk2_0,esk3_0,esk1_0) ),
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
    ( ~ r1_lattice3(k3_lattice3(esk2_0),esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])])).

cnf(c_0_30,negated_conjecture,
    ( r1_lattice3(k3_lattice3(esk2_0),X1,esk3_0)
    | ~ r3_lattice3(esk2_0,esk3_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_21]),c_0_19]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
