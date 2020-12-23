%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1506+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:18 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   27 (  65 expanded)
%              Number of clauses        :   18 (  23 expanded)
%              Number of leaves         :    4 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  114 ( 350 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fraenkel_a_2_1_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & l3_lattices(X2) )
     => ( r2_hidden(X1,a_2_1_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & r3_lattice3(X2,X4,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

fof(t40_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r3_lattice3(X1,X2,X3)
             => r3_lattices(X1,X2,k16_lattice3(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattice3)).

fof(t38_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r2_hidden(X2,X3)
             => ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
                & r3_lattices(X1,k16_lattice3(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).

fof(d22_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] : k16_lattice3(X1,X2) = k15_lattice3(X1,a_2_1_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d22_lattice3)).

fof(c_0_4,plain,(
    ! [X7,X8,X9,X11,X12] :
      ( ( m1_subset_1(esk1_3(X7,X8,X9),u1_struct_0(X8))
        | ~ r2_hidden(X7,a_2_1_lattice3(X8,X9))
        | v2_struct_0(X8)
        | ~ l3_lattices(X8) )
      & ( X7 = esk1_3(X7,X8,X9)
        | ~ r2_hidden(X7,a_2_1_lattice3(X8,X9))
        | v2_struct_0(X8)
        | ~ l3_lattices(X8) )
      & ( r3_lattice3(X8,esk1_3(X7,X8,X9),X9)
        | ~ r2_hidden(X7,a_2_1_lattice3(X8,X9))
        | v2_struct_0(X8)
        | ~ l3_lattices(X8) )
      & ( ~ m1_subset_1(X12,u1_struct_0(X8))
        | X7 != X12
        | ~ r3_lattice3(X8,X12,X11)
        | r2_hidden(X7,a_2_1_lattice3(X8,X11))
        | v2_struct_0(X8)
        | ~ l3_lattices(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_lattice3])])])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( r3_lattice3(X1,X2,X3)
               => r3_lattices(X1,X2,k16_lattice3(X1,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t40_lattice3])).

cnf(c_0_6,plain,
    ( r2_hidden(X3,a_2_1_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattice3(X2,X1,X4)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v10_lattices(esk2_0)
    & v4_lattice3(esk2_0)
    & l3_lattices(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & r3_lattice3(esk2_0,esk3_0,esk4_0)
    & ~ r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X13,X14,X15] :
      ( ( r3_lattices(X13,X14,k15_lattice3(X13,X15))
        | ~ r2_hidden(X14,X15)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v10_lattices(X13)
        | ~ v4_lattice3(X13)
        | ~ l3_lattices(X13) )
      & ( r3_lattices(X13,k16_lattice3(X13,X15),X14)
        | ~ r2_hidden(X14,X15)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v10_lattices(X13)
        | ~ v4_lattice3(X13)
        | ~ l3_lattices(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v4_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(X1,a_2_1_lattice3(esk2_0,X2))
    | ~ r3_lattice3(esk2_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_17,plain,(
    ! [X5,X6] :
      ( v2_struct_0(X5)
      | ~ l3_lattices(X5)
      | k16_lattice3(X5,X6) = k15_lattice3(X5,a_2_1_lattice3(X5,X6)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d22_lattice3])])])])).

cnf(c_0_18,negated_conjecture,
    ( r3_lattices(esk2_0,X1,k15_lattice3(esk2_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_10]),c_0_13]),c_0_14])]),c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk3_0,a_2_1_lattice3(esk2_0,X1))
    | ~ r3_lattice3(esk2_0,esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r3_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | k16_lattice3(X1,X2) = k15_lattice3(X1,a_2_1_lattice3(X1,X2))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r3_lattices(esk2_0,esk3_0,k15_lattice3(esk2_0,X1))
    | ~ r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk3_0,a_2_1_lattice3(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( k15_lattice3(esk2_0,a_2_1_lattice3(esk2_0,X1)) = k16_lattice3(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_10]),c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( ~ r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),
    [proof]).

%------------------------------------------------------------------------------
