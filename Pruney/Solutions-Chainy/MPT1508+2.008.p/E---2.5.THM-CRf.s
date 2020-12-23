%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:03 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 250 expanded)
%              Number of clauses        :   45 (  84 expanded)
%              Number of leaves         :    7 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  463 (1978 expanded)
%              Number of equality atoms :   39 ( 212 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   50 (   5 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

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
    ( ~ v2_struct_0(esk6_0)
    & v10_lattices(esk6_0)
    & v4_lattice3(esk6_0)
    & l3_lattices(esk6_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & r2_hidden(esk7_0,esk8_0)
    & r3_lattice3(esk6_0,esk7_0,esk8_0)
    & k16_lattice3(esk6_0,esk8_0) != esk7_0 ),
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
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( l3_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X24,X25,X26,X28,X29] :
      ( ( m1_subset_1(esk4_3(X24,X25,X26),u1_struct_0(X25))
        | ~ r2_hidden(X24,a_2_1_lattice3(X25,X26))
        | v2_struct_0(X25)
        | ~ l3_lattices(X25) )
      & ( X24 = esk4_3(X24,X25,X26)
        | ~ r2_hidden(X24,a_2_1_lattice3(X25,X26))
        | v2_struct_0(X25)
        | ~ l3_lattices(X25) )
      & ( r3_lattice3(X25,esk4_3(X24,X25,X26),X26)
        | ~ r2_hidden(X24,a_2_1_lattice3(X25,X26))
        | v2_struct_0(X25)
        | ~ l3_lattices(X25) )
      & ( ~ m1_subset_1(X29,u1_struct_0(X25))
        | X24 != X29
        | ~ r3_lattice3(X25,X29,X28)
        | r2_hidden(X24,a_2_1_lattice3(X25,X28))
        | v2_struct_0(X25)
        | ~ l3_lattices(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_lattice3])])])])])])])).

fof(c_0_15,plain,(
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

fof(c_0_16,plain,(
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

cnf(c_0_17,negated_conjecture,
    ( r1_lattices(esk6_0,X1,esk7_0)
    | ~ r2_hidden(esk7_0,X2)
    | ~ r3_lattice3(esk6_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_18,plain,
    ( r3_lattice3(X1,esk4_3(X2,X1,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_1_lattice3(X1,X3))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_lattices(esk6_0,esk4_3(X1,esk6_0,X2),esk7_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk6_0,X2))
    | ~ r2_hidden(esk7_0,X2)
    | ~ m1_subset_1(esk4_3(X1,esk6_0,X2),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_12])]),c_0_13])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( r1_lattices(esk6_0,esk7_0,X1)
    | ~ r4_lattice3(esk6_0,X1,X2)
    | ~ r2_hidden(esk7_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_24,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v4_lattice3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( v10_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( r1_lattices(esk6_0,esk4_3(X1,esk6_0,X2),esk7_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk6_0,X2))
    | ~ r2_hidden(esk7_0,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_12])]),c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_30,plain,(
    ! [X36,X37,X38] :
      ( ( r3_lattices(X36,X37,k15_lattice3(X36,X38))
        | ~ r2_hidden(X37,X38)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v10_lattices(X36)
        | ~ v4_lattice3(X36)
        | ~ l3_lattices(X36) )
      & ( r3_lattices(X36,k16_lattice3(X36,X38),X37)
        | ~ r2_hidden(X37,X38)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v10_lattices(X36)
        | ~ v4_lattice3(X36)
        | ~ l3_lattices(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

fof(c_0_31,plain,(
    ! [X30,X31,X32,X33,X34] :
      ( ( r3_lattice3(X30,X31,X32)
        | X31 != k16_lattice3(X30,X32)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v4_lattice3(X30)
        | ~ l3_lattices(X30) )
      & ( ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ r3_lattice3(X30,X33,X32)
        | r3_lattices(X30,X33,X31)
        | X31 != k16_lattice3(X30,X32)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v4_lattice3(X30)
        | ~ l3_lattices(X30) )
      & ( m1_subset_1(esk5_3(X30,X31,X34),u1_struct_0(X30))
        | ~ r3_lattice3(X30,X31,X34)
        | X31 = k16_lattice3(X30,X34)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v4_lattice3(X30)
        | ~ l3_lattices(X30) )
      & ( r3_lattice3(X30,esk5_3(X30,X31,X34),X34)
        | ~ r3_lattice3(X30,X31,X34)
        | X31 = k16_lattice3(X30,X34)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v4_lattice3(X30)
        | ~ l3_lattices(X30) )
      & ( ~ r3_lattices(X30,esk5_3(X30,X31,X34),X31)
        | ~ r3_lattice3(X30,X31,X34)
        | X31 = k16_lattice3(X30,X34)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v4_lattice3(X30)
        | ~ l3_lattices(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

cnf(c_0_32,negated_conjecture,
    ( X1 = k15_lattice3(esk6_0,X2)
    | r1_lattices(esk6_0,esk7_0,esk3_3(esk6_0,X2,X1))
    | ~ r4_lattice3(esk6_0,esk3_3(esk6_0,X2,X1),X3)
    | ~ r4_lattice3(esk6_0,X1,X2)
    | ~ r2_hidden(esk7_0,X3)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_12])]),c_0_13])).

cnf(c_0_33,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | r4_lattice3(X1,esk3_3(X1,X2,X3),X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(X3,a_2_1_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattice3(X2,X1,X4)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( r1_lattices(esk6_0,esk4_3(X1,esk6_0,esk8_0),esk7_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( X1 = esk4_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,plain,
    ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( X1 = k15_lattice3(esk6_0,X2)
    | r1_lattices(esk6_0,esk7_0,esk3_3(esk6_0,X2,X1))
    | ~ r4_lattice3(esk6_0,X1,X2)
    | ~ r2_hidden(esk7_0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25]),c_0_26]),c_0_12])]),c_0_13])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r1_lattices(esk6_0,X1,esk7_0)
    | ~ r2_hidden(X1,a_2_1_lattice3(esk6_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_12])]),c_0_13])).

cnf(c_0_42,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,plain,
    ( X1 = k16_lattice3(X2,X3)
    | r3_lattices(X2,esk5_3(X2,X1,X3),k15_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ r2_hidden(esk5_3(X2,X1,X3),X4)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( X1 = k15_lattice3(esk6_0,a_2_1_lattice3(X2,X3))
    | r1_lattices(esk6_0,esk7_0,esk3_3(esk6_0,a_2_1_lattice3(X2,X3),X1))
    | v2_struct_0(X2)
    | ~ r4_lattice3(esk6_0,X1,a_2_1_lattice3(X2,X3))
    | ~ r3_lattice3(X2,esk7_0,X3)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r3_lattice3(esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_47,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk2_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_48,negated_conjecture,
    ( r4_lattice3(X1,X2,a_2_1_lattice3(esk6_0,esk8_0))
    | r1_lattices(esk6_0,esk2_3(X1,X2,a_2_1_lattice3(esk6_0,esk8_0)),esk7_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( X1 = k16_lattice3(X2,X3)
    | r3_lattices(X2,esk5_3(X2,X1,X3),k15_lattice3(X2,a_2_1_lattice3(X4,X5)))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ r3_lattice3(X4,esk5_3(X2,X1,X3),X5)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(esk5_3(X2,X1,X3),u1_struct_0(X4))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X4) ),
    inference(spm,[status(thm)],[c_0_43,c_0_40])).

cnf(c_0_50,plain,
    ( r3_lattice3(X1,esk5_3(X1,X2,X3),X3)
    | X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_51,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,esk3_3(X1,X3,X2)) ),
    inference(cn,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( X1 = k15_lattice3(esk6_0,a_2_1_lattice3(esk6_0,esk8_0))
    | r1_lattices(esk6_0,esk7_0,esk3_3(esk6_0,a_2_1_lattice3(esk6_0,esk8_0),X1))
    | ~ r4_lattice3(esk6_0,X1,a_2_1_lattice3(esk6_0,esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_53,negated_conjecture,
    ( r4_lattice3(esk6_0,esk7_0,a_2_1_lattice3(esk6_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_54,plain,
    ( X1 = k16_lattice3(X2,X3)
    | r3_lattices(X2,esk5_3(X2,X1,X3),k15_lattice3(X2,a_2_1_lattice3(X2,X3)))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( k15_lattice3(esk6_0,a_2_1_lattice3(esk6_0,esk8_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_25]),c_0_26]),c_0_53]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_56,plain,
    ( X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,esk5_3(X1,X2,X3),X2)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_57,negated_conjecture,
    ( X1 = k16_lattice3(esk6_0,esk8_0)
    | r3_lattices(esk6_0,esk5_3(esk6_0,X1,esk8_0),esk7_0)
    | ~ r3_lattice3(esk6_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_25]),c_0_26]),c_0_12])]),c_0_13])).

cnf(c_0_58,negated_conjecture,
    ( k16_lattice3(esk6_0,esk8_0) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_25]),c_0_26]),c_0_46]),c_0_11]),c_0_12])]),c_0_58]),c_0_13]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:31:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.19/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.030 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t42_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_lattice3)).
% 0.19/0.41  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 0.19/0.41  fof(fraenkel_a_2_1_lattice3, axiom, ![X1, X2, X3]:((~(v2_struct_0(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_1_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r3_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 0.19/0.41  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 0.19/0.41  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 0.19/0.41  fof(t38_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 0.19/0.41  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 0.19/0.41  fof(c_0_7, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2)))), inference(assume_negation,[status(cth)],[t42_lattice3])).
% 0.19/0.41  fof(c_0_8, plain, ![X5, X6, X7, X8, X9]:((~r3_lattice3(X5,X6,X7)|(~m1_subset_1(X8,u1_struct_0(X5))|(~r2_hidden(X8,X7)|r1_lattices(X5,X6,X8)))|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))&((m1_subset_1(esk1_3(X5,X6,X9),u1_struct_0(X5))|r3_lattice3(X5,X6,X9)|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))&((r2_hidden(esk1_3(X5,X6,X9),X9)|r3_lattice3(X5,X6,X9)|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))&(~r1_lattices(X5,X6,esk1_3(X5,X6,X9))|r3_lattice3(X5,X6,X9)|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.19/0.41  fof(c_0_9, negated_conjecture, ((((~v2_struct_0(esk6_0)&v10_lattices(esk6_0))&v4_lattice3(esk6_0))&l3_lattices(esk6_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&((r2_hidden(esk7_0,esk8_0)&r3_lattice3(esk6_0,esk7_0,esk8_0))&k16_lattice3(esk6_0,esk8_0)!=esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.19/0.41  cnf(c_0_10, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.41  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_12, negated_conjecture, (l3_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_13, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  fof(c_0_14, plain, ![X24, X25, X26, X28, X29]:((((m1_subset_1(esk4_3(X24,X25,X26),u1_struct_0(X25))|~r2_hidden(X24,a_2_1_lattice3(X25,X26))|(v2_struct_0(X25)|~l3_lattices(X25)))&(X24=esk4_3(X24,X25,X26)|~r2_hidden(X24,a_2_1_lattice3(X25,X26))|(v2_struct_0(X25)|~l3_lattices(X25))))&(r3_lattice3(X25,esk4_3(X24,X25,X26),X26)|~r2_hidden(X24,a_2_1_lattice3(X25,X26))|(v2_struct_0(X25)|~l3_lattices(X25))))&(~m1_subset_1(X29,u1_struct_0(X25))|X24!=X29|~r3_lattice3(X25,X29,X28)|r2_hidden(X24,a_2_1_lattice3(X25,X28))|(v2_struct_0(X25)|~l3_lattices(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_lattice3])])])])])])])).
% 0.19/0.41  fof(c_0_15, plain, ![X11, X12, X13, X14, X15]:((~r4_lattice3(X11,X12,X13)|(~m1_subset_1(X14,u1_struct_0(X11))|(~r2_hidden(X14,X13)|r1_lattices(X11,X14,X12)))|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&((m1_subset_1(esk2_3(X11,X12,X15),u1_struct_0(X11))|r4_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&((r2_hidden(esk2_3(X11,X12,X15),X15)|r4_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&(~r1_lattices(X11,esk2_3(X11,X12,X15),X12)|r4_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.19/0.41  fof(c_0_16, plain, ![X17, X18, X19, X20]:(((r4_lattice3(X17,X19,X18)|X19!=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))&(~m1_subset_1(X20,u1_struct_0(X17))|(~r4_lattice3(X17,X20,X18)|r1_lattices(X17,X19,X20))|X19!=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17))))&((m1_subset_1(esk3_3(X17,X18,X19),u1_struct_0(X17))|~r4_lattice3(X17,X19,X18)|X19=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))&((r4_lattice3(X17,esk3_3(X17,X18,X19),X18)|~r4_lattice3(X17,X19,X18)|X19=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))&(~r1_lattices(X17,X19,esk3_3(X17,X18,X19))|~r4_lattice3(X17,X19,X18)|X19=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.19/0.41  cnf(c_0_17, negated_conjecture, (r1_lattices(esk6_0,X1,esk7_0)|~r2_hidden(esk7_0,X2)|~r3_lattice3(esk6_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_18, plain, (r3_lattice3(X1,esk4_3(X2,X1,X3),X3)|v2_struct_0(X1)|~r2_hidden(X2,a_2_1_lattice3(X1,X3))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_19, plain, (r1_lattices(X1,X4,X2)|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  cnf(c_0_20, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_21, negated_conjecture, (r1_lattices(esk6_0,esk4_3(X1,esk6_0,X2),esk7_0)|~r2_hidden(X1,a_2_1_lattice3(esk6_0,X2))|~r2_hidden(esk7_0,X2)|~m1_subset_1(esk4_3(X1,esk6_0,X2),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_22, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_lattice3(X2,X3))|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_23, negated_conjecture, (r1_lattices(esk6_0,esk7_0,X1)|~r4_lattice3(esk6_0,X1,X2)|~r2_hidden(esk7_0,X2)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_24, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_25, negated_conjecture, (v4_lattice3(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_26, negated_conjecture, (v10_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_27, plain, (r4_lattice3(X1,esk3_3(X1,X2,X3),X2)|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_28, negated_conjecture, (r1_lattices(esk6_0,esk4_3(X1,esk6_0,X2),esk7_0)|~r2_hidden(X1,a_2_1_lattice3(esk6_0,X2))|~r2_hidden(esk7_0,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_29, negated_conjecture, (r2_hidden(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  fof(c_0_30, plain, ![X36, X37, X38]:((r3_lattices(X36,X37,k15_lattice3(X36,X38))|~r2_hidden(X37,X38)|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~v10_lattices(X36)|~v4_lattice3(X36)|~l3_lattices(X36)))&(r3_lattices(X36,k16_lattice3(X36,X38),X37)|~r2_hidden(X37,X38)|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~v10_lattices(X36)|~v4_lattice3(X36)|~l3_lattices(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).
% 0.19/0.41  fof(c_0_31, plain, ![X30, X31, X32, X33, X34]:(((r3_lattice3(X30,X31,X32)|X31!=k16_lattice3(X30,X32)|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v4_lattice3(X30)|~l3_lattices(X30)))&(~m1_subset_1(X33,u1_struct_0(X30))|(~r3_lattice3(X30,X33,X32)|r3_lattices(X30,X33,X31))|X31!=k16_lattice3(X30,X32)|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v4_lattice3(X30)|~l3_lattices(X30))))&((m1_subset_1(esk5_3(X30,X31,X34),u1_struct_0(X30))|~r3_lattice3(X30,X31,X34)|X31=k16_lattice3(X30,X34)|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v4_lattice3(X30)|~l3_lattices(X30)))&((r3_lattice3(X30,esk5_3(X30,X31,X34),X34)|~r3_lattice3(X30,X31,X34)|X31=k16_lattice3(X30,X34)|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v4_lattice3(X30)|~l3_lattices(X30)))&(~r3_lattices(X30,esk5_3(X30,X31,X34),X31)|~r3_lattice3(X30,X31,X34)|X31=k16_lattice3(X30,X34)|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v4_lattice3(X30)|~l3_lattices(X30)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.19/0.41  cnf(c_0_32, negated_conjecture, (X1=k15_lattice3(esk6_0,X2)|r1_lattices(esk6_0,esk7_0,esk3_3(esk6_0,X2,X1))|~r4_lattice3(esk6_0,esk3_3(esk6_0,X2,X1),X3)|~r4_lattice3(esk6_0,X1,X2)|~r2_hidden(esk7_0,X3)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_33, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|r4_lattice3(X1,esk3_3(X1,X2,X3),X2)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_34, plain, (r2_hidden(X3,a_2_1_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r3_lattice3(X2,X1,X4)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_35, negated_conjecture, (r1_lattices(esk6_0,esk4_3(X1,esk6_0,esk8_0),esk7_0)|~r2_hidden(X1,a_2_1_lattice3(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.41  cnf(c_0_36, plain, (X1=esk4_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_lattice3(X2,X3))|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_37, plain, (r3_lattices(X1,X2,k15_lattice3(X1,X3))|v2_struct_0(X1)|~r2_hidden(X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_38, plain, (m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))|X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_39, negated_conjecture, (X1=k15_lattice3(esk6_0,X2)|r1_lattices(esk6_0,esk7_0,esk3_3(esk6_0,X2,X1))|~r4_lattice3(esk6_0,X1,X2)|~r2_hidden(esk7_0,X2)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_25]), c_0_26]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_40, plain, (r2_hidden(X1,a_2_1_lattice3(X2,X3))|v2_struct_0(X2)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_34])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (r1_lattices(esk6_0,X1,esk7_0)|~r2_hidden(X1,a_2_1_lattice3(esk6_0,esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_42, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  cnf(c_0_43, plain, (X1=k16_lattice3(X2,X3)|r3_lattices(X2,esk5_3(X2,X1,X3),k15_lattice3(X2,X4))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~r2_hidden(esk5_3(X2,X1,X3),X4)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.41  cnf(c_0_44, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk3_3(X1,X3,X2))|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (X1=k15_lattice3(esk6_0,a_2_1_lattice3(X2,X3))|r1_lattices(esk6_0,esk7_0,esk3_3(esk6_0,a_2_1_lattice3(X2,X3),X1))|v2_struct_0(X2)|~r4_lattice3(esk6_0,X1,a_2_1_lattice3(X2,X3))|~r3_lattice3(X2,esk7_0,X3)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~m1_subset_1(esk7_0,u1_struct_0(X2))|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.41  cnf(c_0_46, negated_conjecture, (r3_lattice3(esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_47, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk2_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  cnf(c_0_48, negated_conjecture, (r4_lattice3(X1,X2,a_2_1_lattice3(esk6_0,esk8_0))|r1_lattices(esk6_0,esk2_3(X1,X2,a_2_1_lattice3(esk6_0,esk8_0)),esk7_0)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.41  cnf(c_0_49, plain, (X1=k16_lattice3(X2,X3)|r3_lattices(X2,esk5_3(X2,X1,X3),k15_lattice3(X2,a_2_1_lattice3(X4,X5)))|v2_struct_0(X4)|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~r3_lattice3(X4,esk5_3(X2,X1,X3),X5)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(esk5_3(X2,X1,X3),u1_struct_0(X4))|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)|~l3_lattices(X4)), inference(spm,[status(thm)],[c_0_43, c_0_40])).
% 0.19/0.41  cnf(c_0_50, plain, (r3_lattice3(X1,esk5_3(X1,X2,X3),X3)|X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_51, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~r1_lattices(X1,X2,esk3_3(X1,X3,X2))), inference(cn,[status(thm)],[c_0_44])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, (X1=k15_lattice3(esk6_0,a_2_1_lattice3(esk6_0,esk8_0))|r1_lattices(esk6_0,esk7_0,esk3_3(esk6_0,a_2_1_lattice3(esk6_0,esk8_0),X1))|~r4_lattice3(esk6_0,X1,a_2_1_lattice3(esk6_0,esk8_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_53, negated_conjecture, (r4_lattice3(esk6_0,esk7_0,a_2_1_lattice3(esk6_0,esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_54, plain, (X1=k16_lattice3(X2,X3)|r3_lattices(X2,esk5_3(X2,X1,X3),k15_lattice3(X2,a_2_1_lattice3(X2,X3)))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_38])).
% 0.19/0.41  cnf(c_0_55, negated_conjecture, (k15_lattice3(esk6_0,a_2_1_lattice3(esk6_0,esk8_0))=esk7_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_25]), c_0_26]), c_0_53]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_56, plain, (X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattices(X1,esk5_3(X1,X2,X3),X2)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (X1=k16_lattice3(esk6_0,esk8_0)|r3_lattices(esk6_0,esk5_3(esk6_0,X1,esk8_0),esk7_0)|~r3_lattice3(esk6_0,X1,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_25]), c_0_26]), c_0_12])]), c_0_13])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (k16_lattice3(esk6_0,esk8_0)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_25]), c_0_26]), c_0_46]), c_0_11]), c_0_12])]), c_0_58]), c_0_13]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 60
% 0.19/0.41  # Proof object clause steps            : 45
% 0.19/0.41  # Proof object formula steps           : 15
% 0.19/0.41  # Proof object conjectures             : 26
% 0.19/0.41  # Proof object clause conjectures      : 23
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 23
% 0.19/0.41  # Proof object initial formulas used   : 7
% 0.19/0.41  # Proof object generating inferences   : 18
% 0.19/0.41  # Proof object simplifying inferences  : 58
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 8
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 33
% 0.19/0.41  # Removed in clause preprocessing      : 0
% 0.19/0.41  # Initial clauses in saturation        : 33
% 0.19/0.41  # Processed clauses                    : 340
% 0.19/0.41  # ...of these trivial                  : 0
% 0.19/0.41  # ...subsumed                          : 67
% 0.19/0.41  # ...remaining for further processing  : 273
% 0.19/0.41  # Other redundant clauses eliminated   : 5
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 11
% 0.19/0.41  # Backward-rewritten                   : 4
% 0.19/0.41  # Generated clauses                    : 381
% 0.19/0.41  # ...of the previous two non-trivial   : 352
% 0.19/0.41  # Contextual simplify-reflections      : 8
% 0.19/0.41  # Paramodulations                      : 376
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 5
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
% 0.19/0.41  # Current number of processed clauses  : 220
% 0.19/0.41  #    Positive orientable unit clauses  : 17
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 2
% 0.19/0.41  #    Non-unit-clauses                  : 201
% 0.19/0.41  # Current number of unprocessed clauses: 77
% 0.19/0.41  # ...number of literals in the above   : 811
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 48
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 4575
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 498
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 86
% 0.19/0.41  # Unit Clause-clause subsumption calls : 4
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 22
% 0.19/0.41  # BW rewrite match successes           : 2
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 18917
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.067 s
% 0.19/0.41  # System time              : 0.006 s
% 0.19/0.41  # Total time               : 0.073 s
% 0.19/0.41  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
