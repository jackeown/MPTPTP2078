%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:03 EST 2020

% Result     : Theorem 0.09s
% Output     : CNFRefutation 0.09s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 385 expanded)
%              Number of clauses        :   66 ( 135 expanded)
%              Number of leaves         :    9 (  95 expanded)
%              Depth                    :   18
%              Number of atoms          :  601 (2965 expanded)
%              Number of equality atoms :   44 ( 302 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   50 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( r2_hidden(X2,X3)
                & r3_lattice3(X1,X2,X3) )
             => k16_lattice3(X1,X3) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).

fof(d16_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r3_lattice3(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X4,X3)
                   => r1_lattices(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

fof(fraenkel_a_2_1_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & l3_lattices(X2) )
     => ( r2_hidden(X1,a_2_1_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & r3_lattice3(X2,X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

fof(d17_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r4_lattice3(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X4,X3)
                   => r1_lattices(X1,X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

fof(d21_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2,X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
           => ( X3 = k15_lattice3(X1,X2)
            <=> ( r4_lattice3(X1,X3,X2)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r4_lattice3(X1,X4,X2)
                     => r1_lattices(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

fof(t40_lattice3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice3)).

fof(t37_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] : k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

fof(fraenkel_a_2_2_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v4_lattice3(X2)
        & l3_lattices(X2) )
     => ( r2_hidden(X1,a_2_2_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & r4_lattice3(X2,X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

fof(t34_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( X2 = k16_lattice3(X1,X3)
            <=> ( r3_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r3_lattice3(X1,X4,X3)
                     => r3_lattices(X1,X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( ( r2_hidden(X2,X3)
                  & r3_lattice3(X1,X2,X3) )
               => k16_lattice3(X1,X3) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t42_lattice3])).

fof(c_0_10,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r3_lattice3(X5,X6,X7)
        | ~ m1_subset_1(X8,u1_struct_0(X5))
        | ~ r2_hidden(X8,X7)
        | r1_lattices(X5,X6,X8)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l3_lattices(X5) )
      & ( m1_subset_1(esk1_3(X5,X6,X9),u1_struct_0(X5))
        | r3_lattice3(X5,X6,X9)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l3_lattices(X5) )
      & ( r2_hidden(esk1_3(X5,X6,X9),X9)
        | r3_lattice3(X5,X6,X9)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l3_lattices(X5) )
      & ( ~ r1_lattices(X5,X6,esk1_3(X5,X6,X9))
        | r3_lattice3(X5,X6,X9)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l3_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v10_lattices(esk7_0)
    & v4_lattice3(esk7_0)
    & l3_lattices(esk7_0)
    & m1_subset_1(esk8_0,u1_struct_0(esk7_0))
    & r2_hidden(esk8_0,esk9_0)
    & r3_lattice3(esk7_0,esk8_0,esk9_0)
    & k16_lattice3(esk7_0,esk9_0) != esk8_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

cnf(c_0_12,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( l3_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X22,X23,X24,X26,X27] :
      ( ( m1_subset_1(esk4_3(X22,X23,X24),u1_struct_0(X23))
        | ~ r2_hidden(X22,a_2_1_lattice3(X23,X24))
        | v2_struct_0(X23)
        | ~ l3_lattices(X23) )
      & ( X22 = esk4_3(X22,X23,X24)
        | ~ r2_hidden(X22,a_2_1_lattice3(X23,X24))
        | v2_struct_0(X23)
        | ~ l3_lattices(X23) )
      & ( r3_lattice3(X23,esk4_3(X22,X23,X24),X24)
        | ~ r2_hidden(X22,a_2_1_lattice3(X23,X24))
        | v2_struct_0(X23)
        | ~ l3_lattices(X23) )
      & ( ~ m1_subset_1(X27,u1_struct_0(X23))
        | X22 != X27
        | ~ r3_lattice3(X23,X27,X26)
        | r2_hidden(X22,a_2_1_lattice3(X23,X26))
        | v2_struct_0(X23)
        | ~ l3_lattices(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_lattice3])])])])])])])).

fof(c_0_17,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r4_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r2_hidden(X14,X13)
        | r1_lattices(X11,X14,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l3_lattices(X11) )
      & ( m1_subset_1(esk2_3(X11,X12,X15),u1_struct_0(X11))
        | r4_lattice3(X11,X12,X15)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l3_lattices(X11) )
      & ( r2_hidden(esk2_3(X11,X12,X15),X15)
        | r4_lattice3(X11,X12,X15)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l3_lattices(X11) )
      & ( ~ r1_lattices(X11,esk2_3(X11,X12,X15),X12)
        | r4_lattice3(X11,X12,X15)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l3_lattices(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

fof(c_0_18,plain,(
    ! [X17,X18,X19,X20] :
      ( ( r4_lattice3(X17,X19,X18)
        | X19 != k15_lattice3(X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ v4_lattice3(X17)
        | ~ l3_lattices(X17)
        | v2_struct_0(X17)
        | ~ l3_lattices(X17) )
      & ( ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r4_lattice3(X17,X20,X18)
        | r1_lattices(X17,X19,X20)
        | X19 != k15_lattice3(X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ v4_lattice3(X17)
        | ~ l3_lattices(X17)
        | v2_struct_0(X17)
        | ~ l3_lattices(X17) )
      & ( m1_subset_1(esk3_3(X17,X18,X19),u1_struct_0(X17))
        | ~ r4_lattice3(X17,X19,X18)
        | X19 = k15_lattice3(X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ v4_lattice3(X17)
        | ~ l3_lattices(X17)
        | v2_struct_0(X17)
        | ~ l3_lattices(X17) )
      & ( r4_lattice3(X17,esk3_3(X17,X18,X19),X18)
        | ~ r4_lattice3(X17,X19,X18)
        | X19 = k15_lattice3(X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ v4_lattice3(X17)
        | ~ l3_lattices(X17)
        | v2_struct_0(X17)
        | ~ l3_lattices(X17) )
      & ( ~ r1_lattices(X17,X19,esk3_3(X17,X18,X19))
        | ~ r4_lattice3(X17,X19,X18)
        | X19 = k15_lattice3(X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ v4_lattice3(X17)
        | ~ l3_lattices(X17)
        | v2_struct_0(X17)
        | ~ l3_lattices(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( r1_lattices(esk7_0,X1,esk8_0)
    | ~ r2_hidden(esk8_0,X2)
    | ~ r3_lattice3(esk7_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_20,plain,
    ( r3_lattice3(X1,esk4_3(X2,X1,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,X3))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r1_lattices(esk7_0,esk4_3(X1,esk7_0,X2),esk8_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk7_0,X2))
    | ~ r2_hidden(esk8_0,X2)
    | ~ m1_subset_1(esk4_3(X1,esk7_0,X2),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_14])]),c_0_15])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( r1_lattices(esk7_0,esk8_0,X1)
    | ~ r4_lattice3(esk7_0,X1,X2)
    | ~ r2_hidden(esk8_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_26,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v4_lattice3(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( v10_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,plain,
    ( r4_lattice3(X1,esk3_3(X1,X2,X3),X2)
    | X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( r1_lattices(esk7_0,esk4_3(X1,esk7_0,X2),esk8_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk7_0,X2))
    | ~ r2_hidden(esk8_0,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_14])]),c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( r2_hidden(X3,a_2_1_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattice3(X2,X1,X4)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k15_lattice3(esk7_0,X2)
    | r1_lattices(esk7_0,esk8_0,esk3_3(esk7_0,X2,X1))
    | ~ r4_lattice3(esk7_0,esk3_3(esk7_0,X2,X1),X3)
    | ~ r4_lattice3(esk7_0,X1,X2)
    | ~ r2_hidden(esk8_0,X3)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_14])]),c_0_15])).

cnf(c_0_34,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | r4_lattice3(X1,esk3_3(X1,X2,X3),X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r1_lattices(esk7_0,esk4_3(X1,esk7_0,esk9_0),esk8_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk7_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( X1 = esk4_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,plain,
    ( r1_lattices(X1,esk4_3(X2,X1,X3),X4)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X4,X5)
    | ~ r2_hidden(esk4_3(X2,X1,X3),X5)
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,X3))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_24])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X42,X43,X44] :
      ( v2_struct_0(X42)
      | ~ v10_lattices(X42)
      | ~ v4_lattice3(X42)
      | ~ l3_lattices(X42)
      | ~ m1_subset_1(X43,u1_struct_0(X42))
      | ~ r3_lattice3(X42,X43,X44)
      | r3_lattices(X42,X43,k16_lattice3(X42,X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_lattice3])])])])).

cnf(c_0_40,negated_conjecture,
    ( X1 = k15_lattice3(esk7_0,X2)
    | r1_lattices(esk7_0,esk8_0,esk3_3(esk7_0,X2,X1))
    | ~ r4_lattice3(esk7_0,X1,X2)
    | ~ r2_hidden(esk8_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_27]),c_0_28]),c_0_14])]),c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( r1_lattices(esk7_0,X1,esk8_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk7_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_14])]),c_0_15])).

cnf(c_0_42,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,plain,
    ( r1_lattices(X1,esk4_3(X2,X1,X3),X4)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X4,a_2_1_lattice3(X5,X6))
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,X3))
    | ~ r3_lattice3(X5,esk4_3(X2,X1,X3),X6)
    | ~ m1_subset_1(esk4_3(X2,X1,X3),u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X5) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,X2,k16_lattice3(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r3_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_45,plain,(
    ! [X40,X41] :
      ( v2_struct_0(X40)
      | ~ v10_lattices(X40)
      | ~ v4_lattice3(X40)
      | ~ l3_lattices(X40)
      | k15_lattice3(X40,X41) = k16_lattice3(X40,a_2_2_lattice3(X40,X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).

cnf(c_0_46,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk3_3(X1,X3,X2))
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( X1 = k15_lattice3(esk7_0,a_2_1_lattice3(X2,X3))
    | r1_lattices(esk7_0,esk8_0,esk3_3(esk7_0,a_2_1_lattice3(X2,X3),X1))
    | v2_struct_0(X2)
    | ~ r4_lattice3(esk7_0,X1,a_2_1_lattice3(X2,X3))
    | ~ r3_lattice3(X2,esk8_0,X3)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(esk8_0,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( r3_lattice3(esk7_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_49,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk2_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( r4_lattice3(X1,X2,a_2_1_lattice3(esk7_0,esk9_0))
    | r1_lattices(esk7_0,esk2_3(X1,X2,a_2_1_lattice3(esk7_0,esk9_0)),esk8_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( r1_lattices(X1,esk4_3(X2,X1,X3),X4)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X4,a_2_1_lattice3(X1,X3))
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,X3))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_20]),c_0_24])).

cnf(c_0_52,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_53,plain,(
    ! [X28,X29,X30,X32,X33] :
      ( ( m1_subset_1(esk5_3(X28,X29,X30),u1_struct_0(X29))
        | ~ r2_hidden(X28,a_2_2_lattice3(X29,X30))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29) )
      & ( X28 = esk5_3(X28,X29,X30)
        | ~ r2_hidden(X28,a_2_2_lattice3(X29,X30))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29) )
      & ( r4_lattice3(X29,esk5_3(X28,X29,X30),X30)
        | ~ r2_hidden(X28,a_2_2_lattice3(X29,X30))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29) )
      & ( ~ m1_subset_1(X33,u1_struct_0(X29))
        | X28 != X33
        | ~ r4_lattice3(X29,X33,X32)
        | r2_hidden(X28,a_2_2_lattice3(X29,X32))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).

cnf(c_0_54,plain,
    ( r3_lattices(X1,esk4_3(X2,X1,X3),k16_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,X3))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_20]),c_0_24])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,esk3_3(X1,X3,X2)) ),
    inference(cn,[status(thm)],[c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( X1 = k15_lattice3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0))
    | r1_lattices(esk7_0,esk8_0,esk3_3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0),X1))
    | ~ r4_lattice3(esk7_0,X1,a_2_1_lattice3(esk7_0,esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_58,negated_conjecture,
    ( r4_lattice3(esk7_0,esk8_0,a_2_1_lattice3(esk7_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_59,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_60,plain,
    ( r1_lattices(X1,esk4_3(X2,X1,X3),esk1_3(X1,X4,X5))
    | r3_lattice3(X1,X4,X5)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,esk1_3(X1,X4,X5),a_2_1_lattice3(X1,X3))
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,X3))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,plain,
    ( r4_lattice3(X1,esk5_3(X2,X1,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_2_lattice3(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( X1 = esk5_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( r3_lattices(X1,esk4_3(X2,X1,a_2_2_lattice3(X1,X3)),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,a_2_2_lattice3(X1,X3)))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( k15_lattice3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0)) = esk8_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_27]),c_0_28]),c_0_58]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_65,plain,
    ( r3_lattice3(X1,esk4_3(X2,X1,X3),X4)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,esk1_3(X1,esk4_3(X2,X1,X3),X4),a_2_1_lattice3(X1,X3))
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,X3))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_24])).

cnf(c_0_66,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ r2_hidden(X2,a_2_2_lattice3(X1,X3))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_68,negated_conjecture,
    ( r3_lattices(esk7_0,esk4_3(X1,esk7_0,a_2_2_lattice3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0))),esk8_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk7_0,a_2_2_lattice3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_27]),c_0_28]),c_0_14])]),c_0_15])).

cnf(c_0_69,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,esk1_3(X1,X2,X3),a_2_1_lattice3(X1,X4))
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,X4))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_36])).

cnf(c_0_70,plain,
    ( r4_lattice3(X1,esk1_3(X2,X3,a_2_2_lattice3(X1,X4)),X4)
    | r3_lattice3(X2,X3,a_2_2_lattice3(X1,X4))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_36])).

cnf(c_0_72,negated_conjecture,
    ( r3_lattices(esk7_0,X1,esk8_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk7_0,a_2_2_lattice3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_36]),c_0_14])]),c_0_15])).

cnf(c_0_73,plain,
    ( r3_lattice3(X1,X2,a_2_2_lattice3(X1,a_2_1_lattice3(X1,X3)))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,X3))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( r3_lattices(esk7_0,X1,esk8_0)
    | ~ r3_lattice3(esk7_0,X1,a_2_2_lattice3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_38]),c_0_14])]),c_0_15])).

cnf(c_0_75,plain,
    ( r3_lattice3(X1,X2,a_2_2_lattice3(X1,a_2_1_lattice3(X1,X3)))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_38])).

fof(c_0_76,plain,(
    ! [X34,X35,X36,X37,X38] :
      ( ( r3_lattice3(X34,X35,X36)
        | X35 != k16_lattice3(X34,X36)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v10_lattices(X34)
        | ~ v4_lattice3(X34)
        | ~ l3_lattices(X34) )
      & ( ~ m1_subset_1(X37,u1_struct_0(X34))
        | ~ r3_lattice3(X34,X37,X36)
        | r3_lattices(X34,X37,X35)
        | X35 != k16_lattice3(X34,X36)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v10_lattices(X34)
        | ~ v4_lattice3(X34)
        | ~ l3_lattices(X34) )
      & ( m1_subset_1(esk6_3(X34,X35,X38),u1_struct_0(X34))
        | ~ r3_lattice3(X34,X35,X38)
        | X35 = k16_lattice3(X34,X38)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v10_lattices(X34)
        | ~ v4_lattice3(X34)
        | ~ l3_lattices(X34) )
      & ( r3_lattice3(X34,esk6_3(X34,X35,X38),X38)
        | ~ r3_lattice3(X34,X35,X38)
        | X35 = k16_lattice3(X34,X38)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v10_lattices(X34)
        | ~ v4_lattice3(X34)
        | ~ l3_lattices(X34) )
      & ( ~ r3_lattices(X34,esk6_3(X34,X35,X38),X35)
        | ~ r3_lattice3(X34,X35,X38)
        | X35 = k16_lattice3(X34,X38)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v10_lattices(X34)
        | ~ v4_lattice3(X34)
        | ~ l3_lattices(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

cnf(c_0_77,negated_conjecture,
    ( r3_lattices(esk7_0,X1,esk8_0)
    | ~ r3_lattice3(esk7_0,X1,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_27]),c_0_28]),c_0_14])]),c_0_15])).

cnf(c_0_78,plain,
    ( r3_lattice3(X1,esk6_3(X1,X2,X3),X3)
    | X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( X1 = k16_lattice3(esk7_0,esk9_0)
    | r3_lattices(esk7_0,esk6_3(esk7_0,X1,esk9_0),esk8_0)
    | ~ r3_lattice3(esk7_0,X1,esk9_0)
    | ~ m1_subset_1(esk6_3(esk7_0,X1,esk9_0),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_27]),c_0_28]),c_0_14])]),c_0_15])).

cnf(c_0_80,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_81,plain,
    ( X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,esk6_3(X1,X2,X3),X2)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( X1 = k16_lattice3(esk7_0,esk9_0)
    | r3_lattices(esk7_0,esk6_3(esk7_0,X1,esk9_0),esk8_0)
    | ~ r3_lattice3(esk7_0,X1,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_27]),c_0_28]),c_0_14])]),c_0_15])).

cnf(c_0_83,negated_conjecture,
    ( k16_lattice3(esk7_0,esk9_0) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_27]),c_0_28]),c_0_48]),c_0_13]),c_0_14])]),c_0_83]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.06/0.25  % Computer   : n013.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 14:19:09 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  # Version: 2.5pre002
% 0.06/0.25  # No SInE strategy applied
% 0.06/0.25  # Trying AutoSched0 for 299 seconds
% 0.09/0.35  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.09/0.35  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.09/0.35  #
% 0.09/0.35  # Preprocessing time       : 0.014 s
% 0.09/0.35  # Presaturation interreduction done
% 0.09/0.35  
% 0.09/0.35  # Proof found!
% 0.09/0.35  # SZS status Theorem
% 0.09/0.35  # SZS output start CNFRefutation
% 0.09/0.35  fof(t42_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_lattice3)).
% 0.09/0.35  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 0.09/0.35  fof(fraenkel_a_2_1_lattice3, axiom, ![X1, X2, X3]:((~(v2_struct_0(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_1_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r3_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 0.09/0.35  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 0.09/0.35  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 0.09/0.35  fof(t40_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)=>r3_lattices(X1,X2,k16_lattice3(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_lattice3)).
% 0.09/0.35  fof(t37_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 0.09/0.35  fof(fraenkel_a_2_2_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_2_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r4_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 0.09/0.35  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 0.09/0.35  fof(c_0_9, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2)))), inference(assume_negation,[status(cth)],[t42_lattice3])).
% 0.09/0.35  fof(c_0_10, plain, ![X5, X6, X7, X8, X9]:((~r3_lattice3(X5,X6,X7)|(~m1_subset_1(X8,u1_struct_0(X5))|(~r2_hidden(X8,X7)|r1_lattices(X5,X6,X8)))|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))&((m1_subset_1(esk1_3(X5,X6,X9),u1_struct_0(X5))|r3_lattice3(X5,X6,X9)|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))&((r2_hidden(esk1_3(X5,X6,X9),X9)|r3_lattice3(X5,X6,X9)|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))&(~r1_lattices(X5,X6,esk1_3(X5,X6,X9))|r3_lattice3(X5,X6,X9)|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.09/0.35  fof(c_0_11, negated_conjecture, ((((~v2_struct_0(esk7_0)&v10_lattices(esk7_0))&v4_lattice3(esk7_0))&l3_lattices(esk7_0))&(m1_subset_1(esk8_0,u1_struct_0(esk7_0))&((r2_hidden(esk8_0,esk9_0)&r3_lattice3(esk7_0,esk8_0,esk9_0))&k16_lattice3(esk7_0,esk9_0)!=esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.09/0.35  cnf(c_0_12, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.09/0.35  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.09/0.35  cnf(c_0_14, negated_conjecture, (l3_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.09/0.35  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.09/0.35  fof(c_0_16, plain, ![X22, X23, X24, X26, X27]:((((m1_subset_1(esk4_3(X22,X23,X24),u1_struct_0(X23))|~r2_hidden(X22,a_2_1_lattice3(X23,X24))|(v2_struct_0(X23)|~l3_lattices(X23)))&(X22=esk4_3(X22,X23,X24)|~r2_hidden(X22,a_2_1_lattice3(X23,X24))|(v2_struct_0(X23)|~l3_lattices(X23))))&(r3_lattice3(X23,esk4_3(X22,X23,X24),X24)|~r2_hidden(X22,a_2_1_lattice3(X23,X24))|(v2_struct_0(X23)|~l3_lattices(X23))))&(~m1_subset_1(X27,u1_struct_0(X23))|X22!=X27|~r3_lattice3(X23,X27,X26)|r2_hidden(X22,a_2_1_lattice3(X23,X26))|(v2_struct_0(X23)|~l3_lattices(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_lattice3])])])])])])])).
% 0.09/0.35  fof(c_0_17, plain, ![X11, X12, X13, X14, X15]:((~r4_lattice3(X11,X12,X13)|(~m1_subset_1(X14,u1_struct_0(X11))|(~r2_hidden(X14,X13)|r1_lattices(X11,X14,X12)))|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&((m1_subset_1(esk2_3(X11,X12,X15),u1_struct_0(X11))|r4_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&((r2_hidden(esk2_3(X11,X12,X15),X15)|r4_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&(~r1_lattices(X11,esk2_3(X11,X12,X15),X12)|r4_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.09/0.35  fof(c_0_18, plain, ![X17, X18, X19, X20]:(((r4_lattice3(X17,X19,X18)|X19!=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))&(~m1_subset_1(X20,u1_struct_0(X17))|(~r4_lattice3(X17,X20,X18)|r1_lattices(X17,X19,X20))|X19!=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17))))&((m1_subset_1(esk3_3(X17,X18,X19),u1_struct_0(X17))|~r4_lattice3(X17,X19,X18)|X19=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))&((r4_lattice3(X17,esk3_3(X17,X18,X19),X18)|~r4_lattice3(X17,X19,X18)|X19=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))&(~r1_lattices(X17,X19,esk3_3(X17,X18,X19))|~r4_lattice3(X17,X19,X18)|X19=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.09/0.35  cnf(c_0_19, negated_conjecture, (r1_lattices(esk7_0,X1,esk8_0)|~r2_hidden(esk8_0,X2)|~r3_lattice3(esk7_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])]), c_0_15])).
% 0.09/0.35  cnf(c_0_20, plain, (r3_lattice3(X1,esk4_3(X2,X1,X3),X3)|v2_struct_0(X1)|~r2_hidden(X2,a_2_1_lattice3(X1,X3))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.09/0.35  cnf(c_0_21, plain, (r1_lattices(X1,X4,X2)|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.09/0.35  cnf(c_0_22, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.09/0.35  cnf(c_0_23, negated_conjecture, (r1_lattices(esk7_0,esk4_3(X1,esk7_0,X2),esk8_0)|~r2_hidden(X1,a_2_1_lattice3(esk7_0,X2))|~r2_hidden(esk8_0,X2)|~m1_subset_1(esk4_3(X1,esk7_0,X2),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_14])]), c_0_15])).
% 0.09/0.35  cnf(c_0_24, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_lattice3(X2,X3))|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.09/0.35  cnf(c_0_25, negated_conjecture, (r1_lattices(esk7_0,esk8_0,X1)|~r4_lattice3(esk7_0,X1,X2)|~r2_hidden(esk8_0,X2)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_13]), c_0_14])]), c_0_15])).
% 0.09/0.35  cnf(c_0_26, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_22])).
% 0.09/0.35  cnf(c_0_27, negated_conjecture, (v4_lattice3(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.09/0.35  cnf(c_0_28, negated_conjecture, (v10_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.09/0.35  cnf(c_0_29, plain, (r4_lattice3(X1,esk3_3(X1,X2,X3),X2)|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.09/0.35  cnf(c_0_30, negated_conjecture, (r1_lattices(esk7_0,esk4_3(X1,esk7_0,X2),esk8_0)|~r2_hidden(X1,a_2_1_lattice3(esk7_0,X2))|~r2_hidden(esk8_0,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_14])]), c_0_15])).
% 0.09/0.35  cnf(c_0_31, negated_conjecture, (r2_hidden(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.09/0.35  cnf(c_0_32, plain, (r2_hidden(X3,a_2_1_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r3_lattice3(X2,X1,X4)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.09/0.35  cnf(c_0_33, negated_conjecture, (X1=k15_lattice3(esk7_0,X2)|r1_lattices(esk7_0,esk8_0,esk3_3(esk7_0,X2,X1))|~r4_lattice3(esk7_0,esk3_3(esk7_0,X2,X1),X3)|~r4_lattice3(esk7_0,X1,X2)|~r2_hidden(esk8_0,X3)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_14])]), c_0_15])).
% 0.09/0.35  cnf(c_0_34, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|r4_lattice3(X1,esk3_3(X1,X2,X3),X2)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_29])).
% 0.09/0.35  cnf(c_0_35, negated_conjecture, (r1_lattices(esk7_0,esk4_3(X1,esk7_0,esk9_0),esk8_0)|~r2_hidden(X1,a_2_1_lattice3(esk7_0,esk9_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.09/0.35  cnf(c_0_36, plain, (X1=esk4_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_lattice3(X2,X3))|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.09/0.35  cnf(c_0_37, plain, (r1_lattices(X1,esk4_3(X2,X1,X3),X4)|v2_struct_0(X1)|~r4_lattice3(X1,X4,X5)|~r2_hidden(esk4_3(X2,X1,X3),X5)|~r2_hidden(X2,a_2_1_lattice3(X1,X3))|~m1_subset_1(X4,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_21, c_0_24])).
% 0.09/0.35  cnf(c_0_38, plain, (r2_hidden(X1,a_2_1_lattice3(X2,X3))|v2_struct_0(X2)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_32])).
% 0.09/0.35  fof(c_0_39, plain, ![X42, X43, X44]:(v2_struct_0(X42)|~v10_lattices(X42)|~v4_lattice3(X42)|~l3_lattices(X42)|(~m1_subset_1(X43,u1_struct_0(X42))|(~r3_lattice3(X42,X43,X44)|r3_lattices(X42,X43,k16_lattice3(X42,X44))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_lattice3])])])])).
% 0.09/0.35  cnf(c_0_40, negated_conjecture, (X1=k15_lattice3(esk7_0,X2)|r1_lattices(esk7_0,esk8_0,esk3_3(esk7_0,X2,X1))|~r4_lattice3(esk7_0,X1,X2)|~r2_hidden(esk8_0,X2)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_27]), c_0_28]), c_0_14])]), c_0_15])).
% 0.09/0.35  cnf(c_0_41, negated_conjecture, (r1_lattices(esk7_0,X1,esk8_0)|~r2_hidden(X1,a_2_1_lattice3(esk7_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_14])]), c_0_15])).
% 0.09/0.35  cnf(c_0_42, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.09/0.35  cnf(c_0_43, plain, (r1_lattices(X1,esk4_3(X2,X1,X3),X4)|v2_struct_0(X5)|v2_struct_0(X1)|~r4_lattice3(X1,X4,a_2_1_lattice3(X5,X6))|~r2_hidden(X2,a_2_1_lattice3(X1,X3))|~r3_lattice3(X5,esk4_3(X2,X1,X3),X6)|~m1_subset_1(esk4_3(X2,X1,X3),u1_struct_0(X5))|~m1_subset_1(X4,u1_struct_0(X1))|~l3_lattices(X1)|~l3_lattices(X5)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.09/0.35  cnf(c_0_44, plain, (v2_struct_0(X1)|r3_lattices(X1,X2,k16_lattice3(X1,X3))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r3_lattice3(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.09/0.35  fof(c_0_45, plain, ![X40, X41]:(v2_struct_0(X40)|~v10_lattices(X40)|~v4_lattice3(X40)|~l3_lattices(X40)|k15_lattice3(X40,X41)=k16_lattice3(X40,a_2_2_lattice3(X40,X41))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).
% 0.09/0.35  cnf(c_0_46, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk3_3(X1,X3,X2))|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.09/0.35  cnf(c_0_47, negated_conjecture, (X1=k15_lattice3(esk7_0,a_2_1_lattice3(X2,X3))|r1_lattices(esk7_0,esk8_0,esk3_3(esk7_0,a_2_1_lattice3(X2,X3),X1))|v2_struct_0(X2)|~r4_lattice3(esk7_0,X1,a_2_1_lattice3(X2,X3))|~r3_lattice3(X2,esk8_0,X3)|~m1_subset_1(X1,u1_struct_0(esk7_0))|~m1_subset_1(esk8_0,u1_struct_0(X2))|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_40, c_0_38])).
% 0.09/0.35  cnf(c_0_48, negated_conjecture, (r3_lattice3(esk7_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.09/0.35  cnf(c_0_49, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk2_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.09/0.35  cnf(c_0_50, negated_conjecture, (r4_lattice3(X1,X2,a_2_1_lattice3(esk7_0,esk9_0))|r1_lattices(esk7_0,esk2_3(X1,X2,a_2_1_lattice3(esk7_0,esk9_0)),esk8_0)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.09/0.35  cnf(c_0_51, plain, (r1_lattices(X1,esk4_3(X2,X1,X3),X4)|v2_struct_0(X1)|~r4_lattice3(X1,X4,a_2_1_lattice3(X1,X3))|~r2_hidden(X2,a_2_1_lattice3(X1,X3))|~m1_subset_1(X4,u1_struct_0(X1))|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_20]), c_0_24])).
% 0.09/0.35  cnf(c_0_52, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.09/0.35  fof(c_0_53, plain, ![X28, X29, X30, X32, X33]:((((m1_subset_1(esk5_3(X28,X29,X30),u1_struct_0(X29))|~r2_hidden(X28,a_2_2_lattice3(X29,X30))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29)))&(X28=esk5_3(X28,X29,X30)|~r2_hidden(X28,a_2_2_lattice3(X29,X30))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29))))&(r4_lattice3(X29,esk5_3(X28,X29,X30),X30)|~r2_hidden(X28,a_2_2_lattice3(X29,X30))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29))))&(~m1_subset_1(X33,u1_struct_0(X29))|X28!=X33|~r4_lattice3(X29,X33,X32)|r2_hidden(X28,a_2_2_lattice3(X29,X32))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).
% 0.09/0.35  cnf(c_0_54, plain, (r3_lattices(X1,esk4_3(X2,X1,X3),k16_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~r2_hidden(X2,a_2_1_lattice3(X1,X3))|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_20]), c_0_24])).
% 0.09/0.35  cnf(c_0_55, plain, (v2_struct_0(X1)|k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.09/0.35  cnf(c_0_56, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~r1_lattices(X1,X2,esk3_3(X1,X3,X2))), inference(cn,[status(thm)],[c_0_46])).
% 0.09/0.35  cnf(c_0_57, negated_conjecture, (X1=k15_lattice3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0))|r1_lattices(esk7_0,esk8_0,esk3_3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0),X1))|~r4_lattice3(esk7_0,X1,a_2_1_lattice3(esk7_0,esk9_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_13]), c_0_14])]), c_0_15])).
% 0.09/0.35  cnf(c_0_58, negated_conjecture, (r4_lattice3(esk7_0,esk8_0,a_2_1_lattice3(esk7_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_13]), c_0_14])]), c_0_15])).
% 0.09/0.35  cnf(c_0_59, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk1_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.09/0.35  cnf(c_0_60, plain, (r1_lattices(X1,esk4_3(X2,X1,X3),esk1_3(X1,X4,X5))|r3_lattice3(X1,X4,X5)|v2_struct_0(X1)|~r4_lattice3(X1,esk1_3(X1,X4,X5),a_2_1_lattice3(X1,X3))|~r2_hidden(X2,a_2_1_lattice3(X1,X3))|~m1_subset_1(X4,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.09/0.35  cnf(c_0_61, plain, (r4_lattice3(X1,esk5_3(X2,X1,X3),X3)|v2_struct_0(X1)|~r2_hidden(X2,a_2_2_lattice3(X1,X3))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.09/0.35  cnf(c_0_62, plain, (X1=esk5_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.09/0.35  cnf(c_0_63, plain, (r3_lattices(X1,esk4_3(X2,X1,a_2_2_lattice3(X1,X3)),k15_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~r2_hidden(X2,a_2_1_lattice3(X1,a_2_2_lattice3(X1,X3)))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.09/0.35  cnf(c_0_64, negated_conjecture, (k15_lattice3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0))=esk8_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_27]), c_0_28]), c_0_58]), c_0_13]), c_0_14])]), c_0_15])).
% 0.09/0.35  cnf(c_0_65, plain, (r3_lattice3(X1,esk4_3(X2,X1,X3),X4)|v2_struct_0(X1)|~r4_lattice3(X1,esk1_3(X1,esk4_3(X2,X1,X3),X4),a_2_1_lattice3(X1,X3))|~r2_hidden(X2,a_2_1_lattice3(X1,X3))|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_24])).
% 0.09/0.35  cnf(c_0_66, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~r2_hidden(X2,a_2_2_lattice3(X1,X3))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.09/0.35  cnf(c_0_67, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.09/0.35  cnf(c_0_68, negated_conjecture, (r3_lattices(esk7_0,esk4_3(X1,esk7_0,a_2_2_lattice3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0))),esk8_0)|~r2_hidden(X1,a_2_1_lattice3(esk7_0,a_2_2_lattice3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_27]), c_0_28]), c_0_14])]), c_0_15])).
% 0.09/0.35  cnf(c_0_69, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r4_lattice3(X1,esk1_3(X1,X2,X3),a_2_1_lattice3(X1,X4))|~r2_hidden(X2,a_2_1_lattice3(X1,X4))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_65, c_0_36])).
% 0.09/0.35  cnf(c_0_70, plain, (r4_lattice3(X1,esk1_3(X2,X3,a_2_2_lattice3(X1,X4)),X4)|r3_lattice3(X2,X3,a_2_2_lattice3(X1,X4))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X2))|~l3_lattices(X1)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.09/0.35  cnf(c_0_71, plain, (m1_subset_1(X1,u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_lattice3(X2,X3))|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_24, c_0_36])).
% 0.09/0.35  cnf(c_0_72, negated_conjecture, (r3_lattices(esk7_0,X1,esk8_0)|~r2_hidden(X1,a_2_1_lattice3(esk7_0,a_2_2_lattice3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_36]), c_0_14])]), c_0_15])).
% 0.09/0.35  cnf(c_0_73, plain, (r3_lattice3(X1,X2,a_2_2_lattice3(X1,a_2_1_lattice3(X1,X3)))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~r2_hidden(X2,a_2_1_lattice3(X1,X3))|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 0.09/0.35  cnf(c_0_74, negated_conjecture, (r3_lattices(esk7_0,X1,esk8_0)|~r3_lattice3(esk7_0,X1,a_2_2_lattice3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0)))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_38]), c_0_14])]), c_0_15])).
% 0.09/0.35  cnf(c_0_75, plain, (r3_lattice3(X1,X2,a_2_2_lattice3(X1,a_2_1_lattice3(X1,X3)))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_73, c_0_38])).
% 0.09/0.35  fof(c_0_76, plain, ![X34, X35, X36, X37, X38]:(((r3_lattice3(X34,X35,X36)|X35!=k16_lattice3(X34,X36)|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~v4_lattice3(X34)|~l3_lattices(X34)))&(~m1_subset_1(X37,u1_struct_0(X34))|(~r3_lattice3(X34,X37,X36)|r3_lattices(X34,X37,X35))|X35!=k16_lattice3(X34,X36)|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~v4_lattice3(X34)|~l3_lattices(X34))))&((m1_subset_1(esk6_3(X34,X35,X38),u1_struct_0(X34))|~r3_lattice3(X34,X35,X38)|X35=k16_lattice3(X34,X38)|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~v4_lattice3(X34)|~l3_lattices(X34)))&((r3_lattice3(X34,esk6_3(X34,X35,X38),X38)|~r3_lattice3(X34,X35,X38)|X35=k16_lattice3(X34,X38)|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~v4_lattice3(X34)|~l3_lattices(X34)))&(~r3_lattices(X34,esk6_3(X34,X35,X38),X35)|~r3_lattice3(X34,X35,X38)|X35=k16_lattice3(X34,X38)|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~v4_lattice3(X34)|~l3_lattices(X34)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.09/0.35  cnf(c_0_77, negated_conjecture, (r3_lattices(esk7_0,X1,esk8_0)|~r3_lattice3(esk7_0,X1,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_27]), c_0_28]), c_0_14])]), c_0_15])).
% 0.09/0.35  cnf(c_0_78, plain, (r3_lattice3(X1,esk6_3(X1,X2,X3),X3)|X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.09/0.35  cnf(c_0_79, negated_conjecture, (X1=k16_lattice3(esk7_0,esk9_0)|r3_lattices(esk7_0,esk6_3(esk7_0,X1,esk9_0),esk8_0)|~r3_lattice3(esk7_0,X1,esk9_0)|~m1_subset_1(esk6_3(esk7_0,X1,esk9_0),u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_27]), c_0_28]), c_0_14])]), c_0_15])).
% 0.09/0.35  cnf(c_0_80, plain, (m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))|X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.09/0.35  cnf(c_0_81, plain, (X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattices(X1,esk6_3(X1,X2,X3),X2)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.09/0.35  cnf(c_0_82, negated_conjecture, (X1=k16_lattice3(esk7_0,esk9_0)|r3_lattices(esk7_0,esk6_3(esk7_0,X1,esk9_0),esk8_0)|~r3_lattice3(esk7_0,X1,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_27]), c_0_28]), c_0_14])]), c_0_15])).
% 0.09/0.35  cnf(c_0_83, negated_conjecture, (k16_lattice3(esk7_0,esk9_0)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.09/0.35  cnf(c_0_84, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_27]), c_0_28]), c_0_48]), c_0_13]), c_0_14])]), c_0_83]), c_0_15]), ['proof']).
% 0.09/0.35  # SZS output end CNFRefutation
% 0.09/0.35  # Proof object total steps             : 85
% 0.09/0.35  # Proof object clause steps            : 66
% 0.09/0.35  # Proof object formula steps           : 19
% 0.09/0.35  # Proof object conjectures             : 31
% 0.09/0.35  # Proof object clause conjectures      : 28
% 0.09/0.35  # Proof object formula conjectures     : 3
% 0.09/0.35  # Proof object initial clauses used    : 29
% 0.09/0.35  # Proof object initial formulas used   : 9
% 0.09/0.35  # Proof object generating inferences   : 33
% 0.09/0.35  # Proof object simplifying inferences  : 82
% 0.09/0.35  # Training examples: 0 positive, 0 negative
% 0.09/0.35  # Parsed axioms                        : 9
% 0.09/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.09/0.35  # Initial clauses                      : 36
% 0.09/0.35  # Removed in clause preprocessing      : 0
% 0.09/0.35  # Initial clauses in saturation        : 36
% 0.09/0.35  # Processed clauses                    : 868
% 0.09/0.35  # ...of these trivial                  : 1
% 0.09/0.35  # ...subsumed                          : 296
% 0.09/0.35  # ...remaining for further processing  : 571
% 0.09/0.35  # Other redundant clauses eliminated   : 6
% 0.09/0.35  # Clauses deleted for lack of memory   : 0
% 0.09/0.35  # Backward-subsumed                    : 15
% 0.09/0.35  # Backward-rewritten                   : 6
% 0.09/0.35  # Generated clauses                    : 1371
% 0.09/0.35  # ...of the previous two non-trivial   : 1265
% 0.09/0.35  # Contextual simplify-reflections      : 19
% 0.09/0.35  # Paramodulations                      : 1365
% 0.09/0.35  # Factorizations                       : 0
% 0.09/0.35  # Equation resolutions                 : 6
% 0.09/0.35  # Propositional unsat checks           : 0
% 0.09/0.35  #    Propositional check models        : 0
% 0.09/0.35  #    Propositional check unsatisfiable : 0
% 0.09/0.35  #    Propositional clauses             : 0
% 0.09/0.35  #    Propositional clauses after purity: 0
% 0.09/0.35  #    Propositional unsat core size     : 0
% 0.09/0.35  #    Propositional preprocessing time  : 0.000
% 0.09/0.35  #    Propositional encoding time       : 0.000
% 0.09/0.35  #    Propositional solver time         : 0.000
% 0.09/0.35  #    Success case prop preproc time    : 0.000
% 0.09/0.35  #    Success case prop encoding time   : 0.000
% 0.09/0.35  #    Success case prop solver time     : 0.000
% 0.09/0.35  # Current number of processed clauses  : 509
% 0.09/0.35  #    Positive orientable unit clauses  : 29
% 0.09/0.35  #    Positive unorientable unit clauses: 0
% 0.09/0.35  #    Negative unit clauses             : 2
% 0.09/0.35  #    Non-unit-clauses                  : 478
% 0.09/0.35  # Current number of unprocessed clauses: 464
% 0.09/0.35  # ...number of literals in the above   : 4270
% 0.09/0.35  # Current number of archived formulas  : 0
% 0.09/0.35  # Current number of archived clauses   : 56
% 0.09/0.35  # Clause-clause subsumption calls (NU) : 41286
% 0.09/0.35  # Rec. Clause-clause subsumption calls : 7114
% 0.09/0.35  # Non-unit clause-clause subsumptions  : 330
% 0.09/0.35  # Unit Clause-clause subsumption calls : 669
% 0.09/0.35  # Rewrite failures with RHS unbound    : 0
% 0.09/0.35  # BW rewrite match attempts            : 141
% 0.09/0.35  # BW rewrite match successes           : 3
% 0.09/0.35  # Condensation attempts                : 0
% 0.09/0.35  # Condensation successes               : 0
% 0.09/0.35  # Termbank termtop insertions          : 62711
% 0.09/0.36  
% 0.09/0.36  # -------------------------------------------------
% 0.09/0.36  # User time                : 0.099 s
% 0.09/0.36  # System time              : 0.006 s
% 0.09/0.36  # Total time               : 0.105 s
% 0.09/0.36  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
