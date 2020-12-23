%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:03 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 290 expanded)
%              Number of clauses        :   48 (  98 expanded)
%              Number of leaves         :    7 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  456 (2210 expanded)
%              Number of equality atoms :   36 ( 237 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   50 (   4 average)
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
    ( ~ v2_struct_0(esk7_0)
    & v10_lattices(esk7_0)
    & v4_lattice3(esk7_0)
    & l3_lattices(esk7_0)
    & m1_subset_1(esk8_0,u1_struct_0(esk7_0))
    & r2_hidden(esk8_0,esk9_0)
    & r3_lattice3(esk7_0,esk8_0,esk9_0)
    & k16_lattice3(esk7_0,esk9_0) != esk8_0 ),
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
    ( m1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( l3_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
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

cnf(c_0_15,negated_conjecture,
    ( r1_lattices(esk7_0,X1,esk8_0)
    | ~ r2_hidden(esk8_0,X2)
    | ~ r3_lattice3(esk7_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_16,plain,
    ( r3_lattice3(X1,esk4_3(X2,X1,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,X3))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

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
    ( r1_lattices(esk7_0,esk4_3(X1,esk7_0,X2),esk8_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk7_0,X2))
    | ~ r2_hidden(esk8_0,X2)
    | ~ m1_subset_1(esk4_3(X1,esk7_0,X2),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_12])]),c_0_13])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

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
    | ~ r2_hidden(esk8_0,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_12])]),c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( r1_lattices(esk7_0,esk8_0,X1)
    | ~ r4_lattice3(esk7_0,X1,X2)
    | ~ r2_hidden(esk8_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_11]),c_0_12])]),c_0_13])).

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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( v10_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

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

cnf(c_0_30,plain,
    ( r2_hidden(X3,a_2_1_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattice3(X2,X1,X4)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( r1_lattices(esk7_0,esk4_3(X1,esk7_0,esk9_0),esk8_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk7_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( X1 = esk4_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_33,plain,(
    ! [X40,X41,X42] :
      ( ( r3_lattices(X40,X41,k15_lattice3(X40,X42))
        | ~ r2_hidden(X41,X42)
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | v2_struct_0(X40)
        | ~ v10_lattices(X40)
        | ~ v4_lattice3(X40)
        | ~ l3_lattices(X40) )
      & ( r3_lattices(X40,k16_lattice3(X40,X42),X41)
        | ~ r2_hidden(X41,X42)
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | v2_struct_0(X40)
        | ~ v10_lattices(X40)
        | ~ v4_lattice3(X40)
        | ~ l3_lattices(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

cnf(c_0_34,negated_conjecture,
    ( X1 = k15_lattice3(esk7_0,X2)
    | r1_lattices(esk7_0,esk8_0,esk3_3(esk7_0,X2,X1))
    | ~ r4_lattice3(esk7_0,esk3_3(esk7_0,X2,X1),X3)
    | ~ r4_lattice3(esk7_0,X1,X2)
    | ~ r2_hidden(esk8_0,X3)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_12])]),c_0_13])).

cnf(c_0_35,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | r4_lattice3(X1,esk3_3(X1,X2,X3),X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r3_lattice3(esk7_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( r1_lattices(esk7_0,X1,esk8_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk7_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_12])]),c_0_13])).

cnf(c_0_39,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,plain,
    ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
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

cnf(c_0_42,negated_conjecture,
    ( X1 = k15_lattice3(esk7_0,X2)
    | r1_lattices(esk7_0,esk8_0,esk3_3(esk7_0,X2,X1))
    | ~ r4_lattice3(esk7_0,X1,X2)
    | ~ r2_hidden(esk8_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_27]),c_0_28]),c_0_12])]),c_0_13])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk8_0,a_2_1_lattice3(esk7_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_44,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk2_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( r4_lattice3(X1,X2,a_2_1_lattice3(esk7_0,esk9_0))
    | r1_lattices(esk7_0,esk2_3(X1,X2,a_2_1_lattice3(esk7_0,esk9_0)),esk8_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( r3_lattices(X1,esk4_3(X2,X1,X3),k15_lattice3(X1,X4))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ r2_hidden(esk4_3(X2,X1,X3),X4)
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,X3))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_20])).

cnf(c_0_47,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),a_2_1_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_16]),c_0_20])).

cnf(c_0_48,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,esk3_3(X1,X3,X2)) ),
    inference(cn,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( X1 = k15_lattice3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0))
    | r1_lattices(esk7_0,esk8_0,esk3_3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0),X1))
    | ~ r4_lattice3(esk7_0,X1,a_2_1_lattice3(esk7_0,esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r4_lattice3(esk7_0,esk8_0,a_2_1_lattice3(esk7_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_51,plain,
    ( r3_lattices(X1,esk4_3(X2,X1,X3),k15_lattice3(X1,a_2_1_lattice3(X1,X3)))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,X3))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k15_lattice3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0)) = esk8_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_27]),c_0_28]),c_0_50]),c_0_11]),c_0_12])]),c_0_13])).

fof(c_0_53,plain,(
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

cnf(c_0_54,negated_conjecture,
    ( r3_lattices(esk7_0,esk4_3(X1,esk7_0,esk9_0),esk8_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk7_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_27]),c_0_28]),c_0_12])]),c_0_13])).

cnf(c_0_55,plain,
    ( r3_lattice3(X1,esk6_3(X1,X2,X3),X3)
    | X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_56,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r3_lattices(esk7_0,X1,esk8_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk7_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_32]),c_0_12])]),c_0_13])).

cnf(c_0_58,plain,
    ( X1 = k16_lattice3(X2,X3)
    | r2_hidden(esk6_3(X2,X1,X3),a_2_1_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_55]),c_0_56])).

cnf(c_0_59,plain,
    ( X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,esk6_3(X1,X2,X3),X2)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( X1 = k16_lattice3(esk7_0,esk9_0)
    | r3_lattices(esk7_0,esk6_3(esk7_0,X1,esk9_0),esk8_0)
    | ~ r3_lattice3(esk7_0,X1,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_27]),c_0_28]),c_0_12])]),c_0_13])).

cnf(c_0_61,negated_conjecture,
    ( k16_lattice3(esk7_0,esk9_0) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_27]),c_0_28]),c_0_37]),c_0_11]),c_0_12])]),c_0_61]),c_0_13]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.20/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.030 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t42_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_lattice3)).
% 0.20/0.41  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 0.20/0.41  fof(fraenkel_a_2_1_lattice3, axiom, ![X1, X2, X3]:((~(v2_struct_0(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_1_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r3_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 0.20/0.41  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 0.20/0.41  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 0.20/0.41  fof(t38_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 0.20/0.41  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 0.20/0.41  fof(c_0_7, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2)))), inference(assume_negation,[status(cth)],[t42_lattice3])).
% 0.20/0.41  fof(c_0_8, plain, ![X5, X6, X7, X8, X9]:((~r3_lattice3(X5,X6,X7)|(~m1_subset_1(X8,u1_struct_0(X5))|(~r2_hidden(X8,X7)|r1_lattices(X5,X6,X8)))|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))&((m1_subset_1(esk1_3(X5,X6,X9),u1_struct_0(X5))|r3_lattice3(X5,X6,X9)|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))&((r2_hidden(esk1_3(X5,X6,X9),X9)|r3_lattice3(X5,X6,X9)|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))&(~r1_lattices(X5,X6,esk1_3(X5,X6,X9))|r3_lattice3(X5,X6,X9)|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.20/0.41  fof(c_0_9, negated_conjecture, ((((~v2_struct_0(esk7_0)&v10_lattices(esk7_0))&v4_lattice3(esk7_0))&l3_lattices(esk7_0))&(m1_subset_1(esk8_0,u1_struct_0(esk7_0))&((r2_hidden(esk8_0,esk9_0)&r3_lattice3(esk7_0,esk8_0,esk9_0))&k16_lattice3(esk7_0,esk9_0)!=esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.20/0.41  cnf(c_0_10, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_12, negated_conjecture, (l3_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_13, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  fof(c_0_14, plain, ![X22, X23, X24, X26, X27]:((((m1_subset_1(esk4_3(X22,X23,X24),u1_struct_0(X23))|~r2_hidden(X22,a_2_1_lattice3(X23,X24))|(v2_struct_0(X23)|~l3_lattices(X23)))&(X22=esk4_3(X22,X23,X24)|~r2_hidden(X22,a_2_1_lattice3(X23,X24))|(v2_struct_0(X23)|~l3_lattices(X23))))&(r3_lattice3(X23,esk4_3(X22,X23,X24),X24)|~r2_hidden(X22,a_2_1_lattice3(X23,X24))|(v2_struct_0(X23)|~l3_lattices(X23))))&(~m1_subset_1(X27,u1_struct_0(X23))|X22!=X27|~r3_lattice3(X23,X27,X26)|r2_hidden(X22,a_2_1_lattice3(X23,X26))|(v2_struct_0(X23)|~l3_lattices(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_lattice3])])])])])])])).
% 0.20/0.41  cnf(c_0_15, negated_conjecture, (r1_lattices(esk7_0,X1,esk8_0)|~r2_hidden(esk8_0,X2)|~r3_lattice3(esk7_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])]), c_0_13])).
% 0.20/0.41  cnf(c_0_16, plain, (r3_lattice3(X1,esk4_3(X2,X1,X3),X3)|v2_struct_0(X1)|~r2_hidden(X2,a_2_1_lattice3(X1,X3))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  fof(c_0_17, plain, ![X11, X12, X13, X14, X15]:((~r4_lattice3(X11,X12,X13)|(~m1_subset_1(X14,u1_struct_0(X11))|(~r2_hidden(X14,X13)|r1_lattices(X11,X14,X12)))|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&((m1_subset_1(esk2_3(X11,X12,X15),u1_struct_0(X11))|r4_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&((r2_hidden(esk2_3(X11,X12,X15),X15)|r4_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&(~r1_lattices(X11,esk2_3(X11,X12,X15),X12)|r4_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.20/0.41  fof(c_0_18, plain, ![X17, X18, X19, X20]:(((r4_lattice3(X17,X19,X18)|X19!=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))&(~m1_subset_1(X20,u1_struct_0(X17))|(~r4_lattice3(X17,X20,X18)|r1_lattices(X17,X19,X20))|X19!=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17))))&((m1_subset_1(esk3_3(X17,X18,X19),u1_struct_0(X17))|~r4_lattice3(X17,X19,X18)|X19=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))&((r4_lattice3(X17,esk3_3(X17,X18,X19),X18)|~r4_lattice3(X17,X19,X18)|X19=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))&(~r1_lattices(X17,X19,esk3_3(X17,X18,X19))|~r4_lattice3(X17,X19,X18)|X19=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.20/0.41  cnf(c_0_19, negated_conjecture, (r1_lattices(esk7_0,esk4_3(X1,esk7_0,X2),esk8_0)|~r2_hidden(X1,a_2_1_lattice3(esk7_0,X2))|~r2_hidden(esk8_0,X2)|~m1_subset_1(esk4_3(X1,esk7_0,X2),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_12])]), c_0_13])).
% 0.20/0.41  cnf(c_0_20, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_lattice3(X2,X3))|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_21, plain, (r1_lattices(X1,X4,X2)|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_22, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_23, negated_conjecture, (r1_lattices(esk7_0,esk4_3(X1,esk7_0,X2),esk8_0)|~r2_hidden(X1,a_2_1_lattice3(esk7_0,X2))|~r2_hidden(esk8_0,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_12])]), c_0_13])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (r2_hidden(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (r1_lattices(esk7_0,esk8_0,X1)|~r4_lattice3(esk7_0,X1,X2)|~r2_hidden(esk8_0,X2)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_11]), c_0_12])]), c_0_13])).
% 0.20/0.41  cnf(c_0_26, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (v4_lattice3(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (v10_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_29, plain, (r4_lattice3(X1,esk3_3(X1,X2,X3),X2)|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_30, plain, (r2_hidden(X3,a_2_1_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r3_lattice3(X2,X1,X4)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_31, negated_conjecture, (r1_lattices(esk7_0,esk4_3(X1,esk7_0,esk9_0),esk8_0)|~r2_hidden(X1,a_2_1_lattice3(esk7_0,esk9_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.41  cnf(c_0_32, plain, (X1=esk4_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_lattice3(X2,X3))|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  fof(c_0_33, plain, ![X40, X41, X42]:((r3_lattices(X40,X41,k15_lattice3(X40,X42))|~r2_hidden(X41,X42)|~m1_subset_1(X41,u1_struct_0(X40))|(v2_struct_0(X40)|~v10_lattices(X40)|~v4_lattice3(X40)|~l3_lattices(X40)))&(r3_lattices(X40,k16_lattice3(X40,X42),X41)|~r2_hidden(X41,X42)|~m1_subset_1(X41,u1_struct_0(X40))|(v2_struct_0(X40)|~v10_lattices(X40)|~v4_lattice3(X40)|~l3_lattices(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (X1=k15_lattice3(esk7_0,X2)|r1_lattices(esk7_0,esk8_0,esk3_3(esk7_0,X2,X1))|~r4_lattice3(esk7_0,esk3_3(esk7_0,X2,X1),X3)|~r4_lattice3(esk7_0,X1,X2)|~r2_hidden(esk8_0,X3)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_12])]), c_0_13])).
% 0.20/0.41  cnf(c_0_35, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|r4_lattice3(X1,esk3_3(X1,X2,X3),X2)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_29])).
% 0.20/0.41  cnf(c_0_36, plain, (r2_hidden(X1,a_2_1_lattice3(X2,X3))|v2_struct_0(X2)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_30])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (r3_lattice3(esk7_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (r1_lattices(esk7_0,X1,esk8_0)|~r2_hidden(X1,a_2_1_lattice3(esk7_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_12])]), c_0_13])).
% 0.20/0.41  cnf(c_0_39, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_40, plain, (r3_lattices(X1,X2,k15_lattice3(X1,X3))|v2_struct_0(X1)|~r2_hidden(X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_41, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk3_3(X1,X3,X2))|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_42, negated_conjecture, (X1=k15_lattice3(esk7_0,X2)|r1_lattices(esk7_0,esk8_0,esk3_3(esk7_0,X2,X1))|~r4_lattice3(esk7_0,X1,X2)|~r2_hidden(esk8_0,X2)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_27]), c_0_28]), c_0_12])]), c_0_13])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (r2_hidden(esk8_0,a_2_1_lattice3(esk7_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_11]), c_0_12])]), c_0_13])).
% 0.20/0.41  cnf(c_0_44, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk2_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (r4_lattice3(X1,X2,a_2_1_lattice3(esk7_0,esk9_0))|r1_lattices(esk7_0,esk2_3(X1,X2,a_2_1_lattice3(esk7_0,esk9_0)),esk8_0)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.41  cnf(c_0_46, plain, (r3_lattices(X1,esk4_3(X2,X1,X3),k15_lattice3(X1,X4))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~r2_hidden(esk4_3(X2,X1,X3),X4)|~r2_hidden(X2,a_2_1_lattice3(X1,X3))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_40, c_0_20])).
% 0.20/0.41  cnf(c_0_47, plain, (r2_hidden(esk4_3(X1,X2,X3),a_2_1_lattice3(X2,X3))|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_lattice3(X2,X3))|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_16]), c_0_20])).
% 0.20/0.41  cnf(c_0_48, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~r1_lattices(X1,X2,esk3_3(X1,X3,X2))), inference(cn,[status(thm)],[c_0_41])).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (X1=k15_lattice3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0))|r1_lattices(esk7_0,esk8_0,esk3_3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0),X1))|~r4_lattice3(esk7_0,X1,a_2_1_lattice3(esk7_0,esk9_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (r4_lattice3(esk7_0,esk8_0,a_2_1_lattice3(esk7_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_11]), c_0_12])]), c_0_13])).
% 0.20/0.41  cnf(c_0_51, plain, (r3_lattices(X1,esk4_3(X2,X1,X3),k15_lattice3(X1,a_2_1_lattice3(X1,X3)))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~r2_hidden(X2,a_2_1_lattice3(X1,X3))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (k15_lattice3(esk7_0,a_2_1_lattice3(esk7_0,esk9_0))=esk8_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_27]), c_0_28]), c_0_50]), c_0_11]), c_0_12])]), c_0_13])).
% 0.20/0.41  fof(c_0_53, plain, ![X34, X35, X36, X37, X38]:(((r3_lattice3(X34,X35,X36)|X35!=k16_lattice3(X34,X36)|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~v4_lattice3(X34)|~l3_lattices(X34)))&(~m1_subset_1(X37,u1_struct_0(X34))|(~r3_lattice3(X34,X37,X36)|r3_lattices(X34,X37,X35))|X35!=k16_lattice3(X34,X36)|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~v4_lattice3(X34)|~l3_lattices(X34))))&((m1_subset_1(esk6_3(X34,X35,X38),u1_struct_0(X34))|~r3_lattice3(X34,X35,X38)|X35=k16_lattice3(X34,X38)|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~v4_lattice3(X34)|~l3_lattices(X34)))&((r3_lattice3(X34,esk6_3(X34,X35,X38),X38)|~r3_lattice3(X34,X35,X38)|X35=k16_lattice3(X34,X38)|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~v4_lattice3(X34)|~l3_lattices(X34)))&(~r3_lattices(X34,esk6_3(X34,X35,X38),X35)|~r3_lattice3(X34,X35,X38)|X35=k16_lattice3(X34,X38)|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v10_lattices(X34)|~v4_lattice3(X34)|~l3_lattices(X34)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, (r3_lattices(esk7_0,esk4_3(X1,esk7_0,esk9_0),esk8_0)|~r2_hidden(X1,a_2_1_lattice3(esk7_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_27]), c_0_28]), c_0_12])]), c_0_13])).
% 0.20/0.41  cnf(c_0_55, plain, (r3_lattice3(X1,esk6_3(X1,X2,X3),X3)|X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.41  cnf(c_0_56, plain, (m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))|X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.41  cnf(c_0_57, negated_conjecture, (r3_lattices(esk7_0,X1,esk8_0)|~r2_hidden(X1,a_2_1_lattice3(esk7_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_32]), c_0_12])]), c_0_13])).
% 0.20/0.41  cnf(c_0_58, plain, (X1=k16_lattice3(X2,X3)|r2_hidden(esk6_3(X2,X1,X3),a_2_1_lattice3(X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_55]), c_0_56])).
% 0.20/0.41  cnf(c_0_59, plain, (X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattices(X1,esk6_3(X1,X2,X3),X2)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (X1=k16_lattice3(esk7_0,esk9_0)|r3_lattices(esk7_0,esk6_3(esk7_0,X1,esk9_0),esk8_0)|~r3_lattice3(esk7_0,X1,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_27]), c_0_28]), c_0_12])]), c_0_13])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (k16_lattice3(esk7_0,esk9_0)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_27]), c_0_28]), c_0_37]), c_0_11]), c_0_12])]), c_0_61]), c_0_13]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 63
% 0.20/0.41  # Proof object clause steps            : 48
% 0.20/0.41  # Proof object formula steps           : 15
% 0.20/0.41  # Proof object conjectures             : 28
% 0.20/0.41  # Proof object clause conjectures      : 25
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 23
% 0.20/0.41  # Proof object initial formulas used   : 7
% 0.20/0.41  # Proof object generating inferences   : 21
% 0.20/0.41  # Proof object simplifying inferences  : 67
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 8
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 36
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 36
% 0.20/0.41  # Processed clauses                    : 290
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 52
% 0.20/0.41  # ...remaining for further processing  : 238
% 0.20/0.41  # Other redundant clauses eliminated   : 6
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 3
% 0.20/0.41  # Backward-rewritten                   : 3
% 0.20/0.41  # Generated clauses                    : 392
% 0.20/0.41  # ...of the previous two non-trivial   : 354
% 0.20/0.41  # Contextual simplify-reflections      : 3
% 0.20/0.41  # Paramodulations                      : 386
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 6
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 190
% 0.20/0.41  #    Positive orientable unit clauses  : 23
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 2
% 0.20/0.41  #    Non-unit-clauses                  : 165
% 0.20/0.41  # Current number of unprocessed clauses: 135
% 0.20/0.41  # ...number of literals in the above   : 1160
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 42
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 4148
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 968
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 58
% 0.20/0.41  # Unit Clause-clause subsumption calls : 69
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 34
% 0.20/0.41  # BW rewrite match successes           : 2
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 16765
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.059 s
% 0.20/0.41  # System time              : 0.008 s
% 0.20/0.41  # Total time               : 0.066 s
% 0.20/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
