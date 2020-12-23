%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:04 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 192 expanded)
%              Number of clauses        :   37 (  65 expanded)
%              Number of leaves         :    7 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  348 (1435 expanded)
%              Number of equality atoms :   29 ( 157 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   40 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(t41_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( r2_hidden(X2,X3)
                & r4_lattice3(X1,X2,X3) )
             => k15_lattice3(X1,X3) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

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

fof(c_0_7,negated_conjecture,(
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

fof(c_0_8,plain,(
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

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v10_lattices(esk5_0)
    & v4_lattice3(esk5_0)
    & l3_lattices(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & r2_hidden(esk6_0,esk7_0)
    & r3_lattice3(esk5_0,esk6_0,esk7_0)
    & k16_lattice3(esk5_0,esk7_0) != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

cnf(c_0_10,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( l3_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X17,X18,X19,X21,X22] :
      ( ( m1_subset_1(esk3_3(X17,X18,X19),u1_struct_0(X18))
        | ~ r2_hidden(X17,a_2_1_lattice3(X18,X19))
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( X17 = esk3_3(X17,X18,X19)
        | ~ r2_hidden(X17,a_2_1_lattice3(X18,X19))
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( r3_lattice3(X18,esk3_3(X17,X18,X19),X19)
        | ~ r2_hidden(X17,a_2_1_lattice3(X18,X19))
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X18))
        | X17 != X22
        | ~ r3_lattice3(X18,X22,X21)
        | r2_hidden(X17,a_2_1_lattice3(X18,X21))
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_lattice3])])])])])])])).

cnf(c_0_15,negated_conjecture,
    ( r1_lattices(esk5_0,X1,esk6_0)
    | ~ r2_hidden(esk6_0,X2)
    | ~ r3_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_16,plain,
    ( r3_lattice3(X1,esk3_3(X2,X1,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,X3))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( r1_lattices(esk5_0,esk3_3(X1,esk5_0,X2),esk6_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk5_0,X2))
    | ~ r2_hidden(esk6_0,X2)
    | ~ m1_subset_1(esk3_3(X1,esk5_0,X2),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_12])]),c_0_13])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X32,X33,X34] :
      ( v2_struct_0(X32)
      | ~ v10_lattices(X32)
      | ~ v4_lattice3(X32)
      | ~ l3_lattices(X32)
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | ~ r2_hidden(X33,X34)
      | ~ r4_lattice3(X32,X33,X34)
      | k15_lattice3(X32,X34) = X33 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_lattice3])])])])).

cnf(c_0_20,negated_conjecture,
    ( r1_lattices(esk5_0,esk3_3(X1,esk5_0,X2),esk6_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk5_0,X2))
    | ~ r2_hidden(esk6_0,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_12])]),c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_22,plain,(
    ! [X29,X30,X31] :
      ( ( r3_lattices(X29,X30,k15_lattice3(X29,X31))
        | ~ r2_hidden(X30,X31)
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29) )
      & ( r3_lattices(X29,k16_lattice3(X29,X31),X30)
        | ~ r2_hidden(X30,X31)
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

fof(c_0_23,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ( r3_lattice3(X23,X24,X25)
        | X24 != k16_lattice3(X23,X25)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v10_lattices(X23)
        | ~ v4_lattice3(X23)
        | ~ l3_lattices(X23) )
      & ( ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ r3_lattice3(X23,X26,X25)
        | r3_lattices(X23,X26,X24)
        | X24 != k16_lattice3(X23,X25)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v10_lattices(X23)
        | ~ v4_lattice3(X23)
        | ~ l3_lattices(X23) )
      & ( m1_subset_1(esk4_3(X23,X24,X27),u1_struct_0(X23))
        | ~ r3_lattice3(X23,X24,X27)
        | X24 = k16_lattice3(X23,X27)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v10_lattices(X23)
        | ~ v4_lattice3(X23)
        | ~ l3_lattices(X23) )
      & ( r3_lattice3(X23,esk4_3(X23,X24,X27),X27)
        | ~ r3_lattice3(X23,X24,X27)
        | X24 = k16_lattice3(X23,X27)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v10_lattices(X23)
        | ~ v4_lattice3(X23)
        | ~ l3_lattices(X23) )
      & ( ~ r3_lattices(X23,esk4_3(X23,X24,X27),X24)
        | ~ r3_lattice3(X23,X24,X27)
        | X24 = k16_lattice3(X23,X27)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v10_lattices(X23)
        | ~ v4_lattice3(X23)
        | ~ l3_lattices(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X3) = X2
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X3)
    | ~ r4_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v4_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( v10_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,a_2_1_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattice3(X2,X1,X4)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( r1_lattices(esk5_0,esk3_3(X1,esk5_0,esk7_0),esk6_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( X1 = esk3_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_30,plain,(
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

cnf(c_0_31,plain,
    ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( k15_lattice3(esk5_0,X1) = esk6_0
    | ~ r4_lattice3(esk5_0,esk6_0,X1)
    | ~ r2_hidden(esk6_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_11]),c_0_25]),c_0_26]),c_0_12])]),c_0_13])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r1_lattices(esk5_0,X1,esk6_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk5_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_12])]),c_0_13])).

cnf(c_0_36,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( X1 = k16_lattice3(X2,X3)
    | r3_lattices(X2,esk4_3(X2,X1,X3),k15_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ r2_hidden(esk4_3(X2,X1,X3),X4)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( k15_lattice3(esk5_0,a_2_1_lattice3(X1,X2)) = esk6_0
    | v2_struct_0(X1)
    | ~ r4_lattice3(esk5_0,esk6_0,a_2_1_lattice3(X1,X2))
    | ~ r3_lattice3(X1,esk6_0,X2)
    | ~ m1_subset_1(esk6_0,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r3_lattice3(esk5_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_40,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk2_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( r4_lattice3(X1,X2,a_2_1_lattice3(esk5_0,esk7_0))
    | r1_lattices(esk5_0,esk2_3(X1,X2,a_2_1_lattice3(esk5_0,esk7_0)),esk6_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( X1 = k16_lattice3(X2,X3)
    | r3_lattices(X2,esk4_3(X2,X1,X3),k15_lattice3(X2,a_2_1_lattice3(X4,X5)))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ r3_lattice3(X4,esk4_3(X2,X1,X3),X5)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(esk4_3(X2,X1,X3),u1_struct_0(X4))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X4) ),
    inference(spm,[status(thm)],[c_0_37,c_0_34])).

cnf(c_0_43,plain,
    ( r3_lattice3(X1,esk4_3(X1,X2,X3),X3)
    | X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( k15_lattice3(esk5_0,a_2_1_lattice3(esk5_0,esk7_0)) = esk6_0
    | ~ r4_lattice3(esk5_0,esk6_0,a_2_1_lattice3(esk5_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( r4_lattice3(esk5_0,esk6_0,a_2_1_lattice3(esk5_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_46,plain,
    ( X1 = k16_lattice3(X2,X3)
    | r3_lattices(X2,esk4_3(X2,X1,X3),k15_lattice3(X2,a_2_1_lattice3(X2,X3)))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( k15_lattice3(esk5_0,a_2_1_lattice3(esk5_0,esk7_0)) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_48,plain,
    ( X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,esk4_3(X1,X2,X3),X2)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( X1 = k16_lattice3(esk5_0,esk7_0)
    | r3_lattices(esk5_0,esk4_3(esk5_0,X1,esk7_0),esk6_0)
    | ~ r3_lattice3(esk5_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_25]),c_0_26]),c_0_12])]),c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( k16_lattice3(esk5_0,esk7_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_25]),c_0_26]),c_0_39]),c_0_11]),c_0_12])]),c_0_50]),c_0_13]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.19/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.029 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t42_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_lattice3)).
% 0.19/0.40  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 0.19/0.40  fof(fraenkel_a_2_1_lattice3, axiom, ![X1, X2, X3]:((~(v2_struct_0(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_1_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r3_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 0.19/0.40  fof(t41_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r4_lattice3(X1,X2,X3))=>k15_lattice3(X1,X3)=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_lattice3)).
% 0.19/0.40  fof(t38_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 0.19/0.40  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 0.19/0.40  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 0.19/0.40  fof(c_0_7, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2)))), inference(assume_negation,[status(cth)],[t42_lattice3])).
% 0.19/0.40  fof(c_0_8, plain, ![X5, X6, X7, X8, X9]:((~r3_lattice3(X5,X6,X7)|(~m1_subset_1(X8,u1_struct_0(X5))|(~r2_hidden(X8,X7)|r1_lattices(X5,X6,X8)))|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))&((m1_subset_1(esk1_3(X5,X6,X9),u1_struct_0(X5))|r3_lattice3(X5,X6,X9)|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))&((r2_hidden(esk1_3(X5,X6,X9),X9)|r3_lattice3(X5,X6,X9)|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))&(~r1_lattices(X5,X6,esk1_3(X5,X6,X9))|r3_lattice3(X5,X6,X9)|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.19/0.40  fof(c_0_9, negated_conjecture, ((((~v2_struct_0(esk5_0)&v10_lattices(esk5_0))&v4_lattice3(esk5_0))&l3_lattices(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&((r2_hidden(esk6_0,esk7_0)&r3_lattice3(esk5_0,esk6_0,esk7_0))&k16_lattice3(esk5_0,esk7_0)!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.19/0.40  cnf(c_0_10, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_12, negated_conjecture, (l3_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_13, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  fof(c_0_14, plain, ![X17, X18, X19, X21, X22]:((((m1_subset_1(esk3_3(X17,X18,X19),u1_struct_0(X18))|~r2_hidden(X17,a_2_1_lattice3(X18,X19))|(v2_struct_0(X18)|~l3_lattices(X18)))&(X17=esk3_3(X17,X18,X19)|~r2_hidden(X17,a_2_1_lattice3(X18,X19))|(v2_struct_0(X18)|~l3_lattices(X18))))&(r3_lattice3(X18,esk3_3(X17,X18,X19),X19)|~r2_hidden(X17,a_2_1_lattice3(X18,X19))|(v2_struct_0(X18)|~l3_lattices(X18))))&(~m1_subset_1(X22,u1_struct_0(X18))|X17!=X22|~r3_lattice3(X18,X22,X21)|r2_hidden(X17,a_2_1_lattice3(X18,X21))|(v2_struct_0(X18)|~l3_lattices(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_lattice3])])])])])])])).
% 0.19/0.40  cnf(c_0_15, negated_conjecture, (r1_lattices(esk5_0,X1,esk6_0)|~r2_hidden(esk6_0,X2)|~r3_lattice3(esk5_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.40  cnf(c_0_16, plain, (r3_lattice3(X1,esk3_3(X2,X1,X3),X3)|v2_struct_0(X1)|~r2_hidden(X2,a_2_1_lattice3(X1,X3))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_17, negated_conjecture, (r1_lattices(esk5_0,esk3_3(X1,esk5_0,X2),esk6_0)|~r2_hidden(X1,a_2_1_lattice3(esk5_0,X2))|~r2_hidden(esk6_0,X2)|~m1_subset_1(esk3_3(X1,esk5_0,X2),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_12])]), c_0_13])).
% 0.19/0.40  cnf(c_0_18, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_lattice3(X2,X3))|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  fof(c_0_19, plain, ![X32, X33, X34]:(v2_struct_0(X32)|~v10_lattices(X32)|~v4_lattice3(X32)|~l3_lattices(X32)|(~m1_subset_1(X33,u1_struct_0(X32))|(~r2_hidden(X33,X34)|~r4_lattice3(X32,X33,X34)|k15_lattice3(X32,X34)=X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_lattice3])])])])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (r1_lattices(esk5_0,esk3_3(X1,esk5_0,X2),esk6_0)|~r2_hidden(X1,a_2_1_lattice3(esk5_0,X2))|~r2_hidden(esk6_0,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_12])]), c_0_13])).
% 0.19/0.40  cnf(c_0_21, negated_conjecture, (r2_hidden(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  fof(c_0_22, plain, ![X29, X30, X31]:((r3_lattices(X29,X30,k15_lattice3(X29,X31))|~r2_hidden(X30,X31)|~m1_subset_1(X30,u1_struct_0(X29))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29)))&(r3_lattices(X29,k16_lattice3(X29,X31),X30)|~r2_hidden(X30,X31)|~m1_subset_1(X30,u1_struct_0(X29))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).
% 0.19/0.40  fof(c_0_23, plain, ![X23, X24, X25, X26, X27]:(((r3_lattice3(X23,X24,X25)|X24!=k16_lattice3(X23,X25)|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v10_lattices(X23)|~v4_lattice3(X23)|~l3_lattices(X23)))&(~m1_subset_1(X26,u1_struct_0(X23))|(~r3_lattice3(X23,X26,X25)|r3_lattices(X23,X26,X24))|X24!=k16_lattice3(X23,X25)|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v10_lattices(X23)|~v4_lattice3(X23)|~l3_lattices(X23))))&((m1_subset_1(esk4_3(X23,X24,X27),u1_struct_0(X23))|~r3_lattice3(X23,X24,X27)|X24=k16_lattice3(X23,X27)|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v10_lattices(X23)|~v4_lattice3(X23)|~l3_lattices(X23)))&((r3_lattice3(X23,esk4_3(X23,X24,X27),X27)|~r3_lattice3(X23,X24,X27)|X24=k16_lattice3(X23,X27)|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v10_lattices(X23)|~v4_lattice3(X23)|~l3_lattices(X23)))&(~r3_lattices(X23,esk4_3(X23,X24,X27),X24)|~r3_lattice3(X23,X24,X27)|X24=k16_lattice3(X23,X27)|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v10_lattices(X23)|~v4_lattice3(X23)|~l3_lattices(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.19/0.41  cnf(c_0_24, plain, (v2_struct_0(X1)|k15_lattice3(X1,X3)=X2|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_hidden(X2,X3)|~r4_lattice3(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_25, negated_conjecture, (v4_lattice3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_26, negated_conjecture, (v10_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_27, plain, (r2_hidden(X3,a_2_1_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r3_lattice3(X2,X1,X4)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_28, negated_conjecture, (r1_lattices(esk5_0,esk3_3(X1,esk5_0,esk7_0),esk6_0)|~r2_hidden(X1,a_2_1_lattice3(esk5_0,esk7_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.41  cnf(c_0_29, plain, (X1=esk3_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_lattice3(X2,X3))|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  fof(c_0_30, plain, ![X11, X12, X13, X14, X15]:((~r4_lattice3(X11,X12,X13)|(~m1_subset_1(X14,u1_struct_0(X11))|(~r2_hidden(X14,X13)|r1_lattices(X11,X14,X12)))|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&((m1_subset_1(esk2_3(X11,X12,X15),u1_struct_0(X11))|r4_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&((r2_hidden(esk2_3(X11,X12,X15),X15)|r4_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&(~r1_lattices(X11,esk2_3(X11,X12,X15),X12)|r4_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.19/0.41  cnf(c_0_31, plain, (r3_lattices(X1,X2,k15_lattice3(X1,X3))|v2_struct_0(X1)|~r2_hidden(X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_32, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.41  cnf(c_0_33, negated_conjecture, (k15_lattice3(esk5_0,X1)=esk6_0|~r4_lattice3(esk5_0,esk6_0,X1)|~r2_hidden(esk6_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_11]), c_0_25]), c_0_26]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_34, plain, (r2_hidden(X1,a_2_1_lattice3(X2,X3))|v2_struct_0(X2)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_35, negated_conjecture, (r1_lattices(esk5_0,X1,esk6_0)|~r2_hidden(X1,a_2_1_lattice3(esk5_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_36, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_37, plain, (X1=k16_lattice3(X2,X3)|r3_lattices(X2,esk4_3(X2,X1,X3),k15_lattice3(X2,X4))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~r2_hidden(esk4_3(X2,X1,X3),X4)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.41  cnf(c_0_38, negated_conjecture, (k15_lattice3(esk5_0,a_2_1_lattice3(X1,X2))=esk6_0|v2_struct_0(X1)|~r4_lattice3(esk5_0,esk6_0,a_2_1_lattice3(X1,X2))|~r3_lattice3(X1,esk6_0,X2)|~m1_subset_1(esk6_0,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.41  cnf(c_0_39, negated_conjecture, (r3_lattice3(esk5_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_40, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk2_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (r4_lattice3(X1,X2,a_2_1_lattice3(esk5_0,esk7_0))|r1_lattices(esk5_0,esk2_3(X1,X2,a_2_1_lattice3(esk5_0,esk7_0)),esk6_0)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.41  cnf(c_0_42, plain, (X1=k16_lattice3(X2,X3)|r3_lattices(X2,esk4_3(X2,X1,X3),k15_lattice3(X2,a_2_1_lattice3(X4,X5)))|v2_struct_0(X4)|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~r3_lattice3(X4,esk4_3(X2,X1,X3),X5)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(esk4_3(X2,X1,X3),u1_struct_0(X4))|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)|~l3_lattices(X4)), inference(spm,[status(thm)],[c_0_37, c_0_34])).
% 0.19/0.41  cnf(c_0_43, plain, (r3_lattice3(X1,esk4_3(X1,X2,X3),X3)|X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (k15_lattice3(esk5_0,a_2_1_lattice3(esk5_0,esk7_0))=esk6_0|~r4_lattice3(esk5_0,esk6_0,a_2_1_lattice3(esk5_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (r4_lattice3(esk5_0,esk6_0,a_2_1_lattice3(esk5_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_46, plain, (X1=k16_lattice3(X2,X3)|r3_lattices(X2,esk4_3(X2,X1,X3),k15_lattice3(X2,a_2_1_lattice3(X2,X3)))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_32])).
% 0.19/0.41  cnf(c_0_47, negated_conjecture, (k15_lattice3(esk5_0,a_2_1_lattice3(esk5_0,esk7_0))=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])])).
% 0.19/0.41  cnf(c_0_48, plain, (X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattices(X1,esk4_3(X1,X2,X3),X2)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.41  cnf(c_0_49, negated_conjecture, (X1=k16_lattice3(esk5_0,esk7_0)|r3_lattices(esk5_0,esk4_3(esk5_0,X1,esk7_0),esk6_0)|~r3_lattice3(esk5_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_25]), c_0_26]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_50, negated_conjecture, (k16_lattice3(esk5_0,esk7_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_25]), c_0_26]), c_0_39]), c_0_11]), c_0_12])]), c_0_50]), c_0_13]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 52
% 0.19/0.41  # Proof object clause steps            : 37
% 0.19/0.41  # Proof object formula steps           : 15
% 0.19/0.41  # Proof object conjectures             : 24
% 0.19/0.41  # Proof object clause conjectures      : 21
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 20
% 0.19/0.41  # Proof object initial formulas used   : 7
% 0.19/0.41  # Proof object generating inferences   : 15
% 0.19/0.41  # Proof object simplifying inferences  : 42
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 7
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 28
% 0.19/0.41  # Removed in clause preprocessing      : 0
% 0.19/0.41  # Initial clauses in saturation        : 28
% 0.19/0.41  # Processed clauses                    : 265
% 0.19/0.41  # ...of these trivial                  : 0
% 0.19/0.41  # ...subsumed                          : 42
% 0.19/0.41  # ...remaining for further processing  : 223
% 0.19/0.41  # Other redundant clauses eliminated   : 3
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 6
% 0.19/0.41  # Backward-rewritten                   : 4
% 0.19/0.41  # Generated clauses                    : 301
% 0.19/0.41  # ...of the previous two non-trivial   : 289
% 0.19/0.41  # Contextual simplify-reflections      : 11
% 0.19/0.41  # Paramodulations                      : 298
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 3
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 182
% 0.19/0.41  #    Positive orientable unit clauses  : 14
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 2
% 0.19/0.41  #    Non-unit-clauses                  : 166
% 0.19/0.41  # Current number of unprocessed clauses: 79
% 0.19/0.41  # ...number of literals in the above   : 838
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 38
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 4240
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 430
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 59
% 0.19/0.41  # Unit Clause-clause subsumption calls : 17
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 20
% 0.19/0.41  # BW rewrite match successes           : 3
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 15342
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.058 s
% 0.19/0.41  # System time              : 0.007 s
% 0.19/0.41  # Total time               : 0.065 s
% 0.19/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
