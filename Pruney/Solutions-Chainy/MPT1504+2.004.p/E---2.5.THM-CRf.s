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
% DateTime   : Thu Dec  3 11:14:59 EST 2020

% Result     : Theorem 56.84s
% Output     : CNFRefutation 56.84s
% Verified   : 
% Statistics : Number of formulae       :   98 (25042 expanded)
%              Number of clauses        :   79 (8749 expanded)
%              Number of leaves         :    9 (6119 expanded)
%              Depth                    :   34
%              Number of atoms          :  583 (141903 expanded)
%              Number of equality atoms :   85 (17858 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   50 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] : k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).

fof(dt_k16_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

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

fof(d22_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] : k16_lattice3(X1,X2) = k15_lattice3(X1,a_2_1_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d22_lattice3)).

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

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2] : k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t37_lattice3])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v10_lattices(esk7_0)
    & v4_lattice3(esk7_0)
    & l3_lattices(esk7_0)
    & k15_lattice3(esk7_0,esk8_0) != k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_11,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | ~ l3_lattices(X24)
      | m1_subset_1(k16_lattice3(X24,X25),u1_struct_0(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

fof(c_0_12,plain,(
    ! [X38,X39,X40,X41,X42] :
      ( ( r3_lattice3(X38,X39,X40)
        | X39 != k16_lattice3(X38,X40)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ v10_lattices(X38)
        | ~ v4_lattice3(X38)
        | ~ l3_lattices(X38) )
      & ( ~ m1_subset_1(X41,u1_struct_0(X38))
        | ~ r3_lattice3(X38,X41,X40)
        | r3_lattices(X38,X41,X39)
        | X39 != k16_lattice3(X38,X40)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ v10_lattices(X38)
        | ~ v4_lattice3(X38)
        | ~ l3_lattices(X38) )
      & ( m1_subset_1(esk6_3(X38,X39,X42),u1_struct_0(X38))
        | ~ r3_lattice3(X38,X39,X42)
        | X39 = k16_lattice3(X38,X42)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ v10_lattices(X38)
        | ~ v4_lattice3(X38)
        | ~ l3_lattices(X38) )
      & ( r3_lattice3(X38,esk6_3(X38,X39,X42),X42)
        | ~ r3_lattice3(X38,X39,X42)
        | X39 = k16_lattice3(X38,X42)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ v10_lattices(X38)
        | ~ v4_lattice3(X38)
        | ~ l3_lattices(X38) )
      & ( ~ r3_lattices(X38,esk6_3(X38,X39,X42),X39)
        | ~ r3_lattice3(X38,X39,X42)
        | X39 = k16_lattice3(X38,X42)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ v10_lattices(X38)
        | ~ v4_lattice3(X38)
        | ~ l3_lattices(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

fof(c_0_13,plain,(
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

fof(c_0_14,plain,(
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

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( l3_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_18,plain,(
    ! [X32,X33,X34,X36,X37] :
      ( ( m1_subset_1(esk5_3(X32,X33,X34),u1_struct_0(X33))
        | ~ r2_hidden(X32,a_2_2_lattice3(X33,X34))
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ v4_lattice3(X33)
        | ~ l3_lattices(X33) )
      & ( X32 = esk5_3(X32,X33,X34)
        | ~ r2_hidden(X32,a_2_2_lattice3(X33,X34))
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ v4_lattice3(X33)
        | ~ l3_lattices(X33) )
      & ( r4_lattice3(X33,esk5_3(X32,X33,X34),X34)
        | ~ r2_hidden(X32,a_2_2_lattice3(X33,X34))
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ v4_lattice3(X33)
        | ~ l3_lattices(X33) )
      & ( ~ m1_subset_1(X37,u1_struct_0(X33))
        | X32 != X37
        | ~ r4_lattice3(X33,X37,X36)
        | r2_hidden(X32,a_2_2_lattice3(X33,X36))
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ v4_lattice3(X33)
        | ~ l3_lattices(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).

fof(c_0_19,plain,(
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

cnf(c_0_20,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k16_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(k16_lattice3(esk7_0,X1),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_24,plain,
    ( r2_hidden(X3,a_2_2_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r4_lattice3(X2,X1,X4)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r3_lattice3(X1,k16_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]),c_0_16])).

cnf(c_0_28,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r4_lattice3(esk7_0,k16_lattice3(esk7_0,X1),X2)
    | m1_subset_1(esk2_3(esk7_0,k16_lattice3(esk7_0,X1),X2),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_17])]),c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( v4_lattice3(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,negated_conjecture,
    ( v10_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | r4_lattice3(X1,esk3_3(X1,X2,X3),X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( r1_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( k16_lattice3(esk7_0,X1) = k15_lattice3(esk7_0,X2)
    | m1_subset_1(esk2_3(esk7_0,k16_lattice3(esk7_0,X1),X2),u1_struct_0(esk7_0))
    | m1_subset_1(esk3_3(esk7_0,X2,k16_lattice3(esk7_0,X1)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_23]),c_0_17])]),c_0_15])).

cnf(c_0_36,plain,
    ( X1 = k15_lattice3(X2,X3)
    | r2_hidden(esk3_3(X2,X3,X1),a_2_2_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_28])).

cnf(c_0_37,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_38,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ l3_lattices(X22)
      | k16_lattice3(X22,X23) = k15_lattice3(X22,a_2_1_lattice3(X22,X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d22_lattice3])])])])).

cnf(c_0_39,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( k16_lattice3(esk7_0,X1) = k15_lattice3(esk7_0,X2)
    | r1_lattices(esk7_0,k16_lattice3(esk7_0,X3),esk3_3(esk7_0,X2,k16_lattice3(esk7_0,X1)))
    | m1_subset_1(esk2_3(esk7_0,k16_lattice3(esk7_0,X1),X2),u1_struct_0(esk7_0))
    | ~ r2_hidden(esk3_3(esk7_0,X2,k16_lattice3(esk7_0,X1)),X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_30]),c_0_31]),c_0_17])]),c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( k16_lattice3(esk7_0,X1) = k15_lattice3(esk7_0,X2)
    | r2_hidden(esk3_3(esk7_0,X2,k16_lattice3(esk7_0,X1)),a_2_2_lattice3(esk7_0,X2))
    | m1_subset_1(esk2_3(esk7_0,k16_lattice3(esk7_0,X1),X2),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_29]),c_0_30]),c_0_31]),c_0_23]),c_0_17])]),c_0_15])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | r4_lattice3(X1,X2,X3)
    | X2 != k15_lattice3(X1,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | k16_lattice3(X1,X2) = k15_lattice3(X1,a_2_1_lattice3(X1,X2))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_44,plain,(
    ! [X26,X27,X28,X30,X31] :
      ( ( m1_subset_1(esk4_3(X26,X27,X28),u1_struct_0(X27))
        | ~ r2_hidden(X26,a_2_1_lattice3(X27,X28))
        | v2_struct_0(X27)
        | ~ l3_lattices(X27) )
      & ( X26 = esk4_3(X26,X27,X28)
        | ~ r2_hidden(X26,a_2_1_lattice3(X27,X28))
        | v2_struct_0(X27)
        | ~ l3_lattices(X27) )
      & ( r3_lattice3(X27,esk4_3(X26,X27,X28),X28)
        | ~ r2_hidden(X26,a_2_1_lattice3(X27,X28))
        | v2_struct_0(X27)
        | ~ l3_lattices(X27) )
      & ( ~ m1_subset_1(X31,u1_struct_0(X27))
        | X26 != X31
        | ~ r3_lattice3(X27,X31,X30)
        | r2_hidden(X26,a_2_1_lattice3(X27,X30))
        | v2_struct_0(X27)
        | ~ l3_lattices(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_lattice3])])])])])])])).

cnf(c_0_45,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,esk3_3(X1,X3,X2)) ),
    inference(cn,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( k16_lattice3(esk7_0,X1) = k15_lattice3(esk7_0,X2)
    | r1_lattices(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X2)),esk3_3(esk7_0,X2,k16_lattice3(esk7_0,X1)))
    | m1_subset_1(esk2_3(esk7_0,k16_lattice3(esk7_0,X1),X2),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( r4_lattice3(X1,k15_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k15_lattice3(esk7_0,a_2_1_lattice3(esk7_0,X1)) = k16_lattice3(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_43]),c_0_17])])).

cnf(c_0_49,plain,
    ( r2_hidden(X3,a_2_1_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattice3(X2,X1,X4)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | m1_subset_1(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_30]),c_0_31]),c_0_23]),c_0_17])]),c_0_15]),c_0_29])).

cnf(c_0_52,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,negated_conjecture,
    ( r4_lattice3(esk7_0,k16_lattice3(esk7_0,X1),a_2_1_lattice3(esk7_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_30]),c_0_31]),c_0_23]),c_0_17])]),c_0_15])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r2_hidden(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),X2),X2)
    | r3_lattice3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_17])]),c_0_15])).

cnf(c_0_56,negated_conjecture,
    ( r1_lattices(esk7_0,X1,k16_lattice3(esk7_0,X2))
    | ~ r2_hidden(X1,a_2_1_lattice3(esk7_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_23]),c_0_17])]),c_0_15])).

cnf(c_0_57,plain,
    ( X1 = esk5_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_58,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r2_hidden(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),X2),X2)
    | r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,X2)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_17])]),c_0_15]),c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r1_lattices(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),k16_lattice3(esk7_0,X2))
    | ~ r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,X2)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(X2,X3)),X2,X3) = esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(X2,X3))
    | k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,a_2_2_lattice3(X2,X3)))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk2_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_62,negated_conjecture,
    ( esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(X2,X3)),X2,X3) = esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(X2,X3))
    | k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r1_lattices(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),k16_lattice3(esk7_0,a_2_2_lattice3(X2,X3)))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)),esk7_0,X1) = esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1))
    | k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r4_lattice3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_23]),c_0_17]),c_0_30]),c_0_31])]),c_0_15])).

cnf(c_0_64,negated_conjecture,
    ( esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)),esk7_0,X1) = esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1))
    | k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | m1_subset_1(esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_63]),c_0_30]),c_0_31]),c_0_23]),c_0_17])]),c_0_15])).

cnf(c_0_65,negated_conjecture,
    ( esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)),esk7_0,X1) = esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1))
    | k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r1_lattices(esk7_0,k16_lattice3(esk7_0,X2),esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))))
    | ~ r2_hidden(esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_64]),c_0_30]),c_0_31]),c_0_17])]),c_0_15])).

cnf(c_0_66,negated_conjecture,
    ( esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)),esk7_0,X1) = esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1))
    | k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r2_hidden(esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))),a_2_2_lattice3(esk7_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_63]),c_0_30]),c_0_31]),c_0_23]),c_0_17])]),c_0_15])).

cnf(c_0_67,plain,
    ( r4_lattice3(X1,esk5_3(X2,X1,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_2_lattice3(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_68,negated_conjecture,
    ( esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)),esk7_0,X1) = esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1))
    | k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r1_lattices(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_69,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_70,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r4_lattice3(X2,esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(X2,X3)),X2,X3),X3)
    | r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,a_2_2_lattice3(X2,X3)))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_58])).

cnf(c_0_71,negated_conjecture,
    ( esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)),esk7_0,X1) = esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1))
    | k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_68]),c_0_30]),c_0_31]),c_0_23]),c_0_17])]),c_0_15]),c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r3_lattice3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),X2)
    | m1_subset_1(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),X2),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_51]),c_0_17])]),c_0_15])).

cnf(c_0_73,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r4_lattice3(esk7_0,esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)),X1)
    | r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_30]),c_0_31]),c_0_17])]),c_0_15])).

cnf(c_0_74,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,X2))
    | m1_subset_1(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),X2),u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_72]),c_0_17])]),c_0_15]),c_0_51])).

cnf(c_0_75,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_76,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r1_lattices(esk7_0,X2,esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)))
    | r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_73]),c_0_17])]),c_0_15]),c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( r4_lattice3(esk7_0,k16_lattice3(esk7_0,X1),X2)
    | r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,X1),X2),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_23]),c_0_17])]),c_0_15])).

cnf(c_0_78,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X2)) = k15_lattice3(esk7_0,X2)
    | r1_lattices(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X2)),X2),a_2_2_lattice3(esk7_0,X2)))
    | r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X2)),X2),a_2_1_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X2)))
    | ~ r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_51])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,X1),X2),X2)
    | r2_hidden(k16_lattice3(esk7_0,X1),a_2_2_lattice3(esk7_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_77]),c_0_30]),c_0_31]),c_0_23]),c_0_17])]),c_0_15])).

cnf(c_0_80,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_81,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r1_lattices(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)))
    | r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)))
    | r2_hidden(k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),a_2_2_lattice3(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(k16_lattice3(esk7_0,X1),a_2_2_lattice3(esk7_0,X2))
    | m1_subset_1(esk2_3(esk7_0,k16_lattice3(esk7_0,X1),X2),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_29]),c_0_30]),c_0_31]),c_0_23]),c_0_17])]),c_0_15])).

cnf(c_0_83,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)))
    | r2_hidden(k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),a_2_2_lattice3(esk7_0,X1))
    | r3_lattice3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_17])]),c_0_15]),c_0_82])).

cnf(c_0_84,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)))
    | r2_hidden(k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),a_2_2_lattice3(esk7_0,X1)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_83]),c_0_17])]),c_0_15]),c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r1_lattices(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)))
    | r2_hidden(k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),a_2_2_lattice3(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r4_lattice3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1)
    | r2_hidden(k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),a_2_2_lattice3(esk7_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_85]),c_0_23]),c_0_17])]),c_0_15])).

cnf(c_0_87,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r2_hidden(k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),a_2_2_lattice3(esk7_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_86]),c_0_30]),c_0_31]),c_0_23]),c_0_17])]),c_0_15])).

cnf(c_0_88,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r4_lattice3(esk7_0,esk5_3(k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),esk7_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_87]),c_0_30]),c_0_31]),c_0_17])]),c_0_15])).

cnf(c_0_89,negated_conjecture,
    ( esk5_3(k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),esk7_0,X1) = k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))
    | k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_87]),c_0_30]),c_0_31]),c_0_17])]),c_0_15])).

cnf(c_0_90,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r4_lattice3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_91,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | m1_subset_1(esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_90]),c_0_30]),c_0_31]),c_0_23]),c_0_17])]),c_0_15])).

cnf(c_0_92,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r1_lattices(esk7_0,k16_lattice3(esk7_0,X2),esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))))
    | ~ r2_hidden(esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_91]),c_0_30]),c_0_31]),c_0_17])]),c_0_15])).

cnf(c_0_93,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r2_hidden(esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))),a_2_2_lattice3(esk7_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_90]),c_0_30]),c_0_31]),c_0_23]),c_0_17])]),c_0_15])).

cnf(c_0_94,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1)
    | r1_lattices(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_95,negated_conjecture,
    ( k15_lattice3(esk7_0,esk8_0) != k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_96,negated_conjecture,
    ( k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_94]),c_0_30]),c_0_31]),c_0_23]),c_0_17])]),c_0_15]),c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:16:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 56.84/57.06  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 56.84/57.06  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 56.84/57.06  #
% 56.84/57.06  # Preprocessing time       : 0.029 s
% 56.84/57.06  # Presaturation interreduction done
% 56.84/57.06  
% 56.84/57.06  # Proof found!
% 56.84/57.06  # SZS status Theorem
% 56.84/57.06  # SZS output start CNFRefutation
% 56.84/57.06  fof(t37_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_lattice3)).
% 56.84/57.06  fof(dt_k16_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 56.84/57.06  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 56.84/57.06  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 56.84/57.06  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 56.84/57.06  fof(fraenkel_a_2_2_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_2_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r4_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 56.84/57.06  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 56.84/57.06  fof(d22_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:k16_lattice3(X1,X2)=k15_lattice3(X1,a_2_1_lattice3(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d22_lattice3)).
% 56.84/57.06  fof(fraenkel_a_2_1_lattice3, axiom, ![X1, X2, X3]:((~(v2_struct_0(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_1_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r3_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 56.84/57.06  fof(c_0_9, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2)))), inference(assume_negation,[status(cth)],[t37_lattice3])).
% 56.84/57.06  fof(c_0_10, negated_conjecture, ((((~v2_struct_0(esk7_0)&v10_lattices(esk7_0))&v4_lattice3(esk7_0))&l3_lattices(esk7_0))&k15_lattice3(esk7_0,esk8_0)!=k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 56.84/57.06  fof(c_0_11, plain, ![X24, X25]:(v2_struct_0(X24)|~l3_lattices(X24)|m1_subset_1(k16_lattice3(X24,X25),u1_struct_0(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).
% 56.84/57.06  fof(c_0_12, plain, ![X38, X39, X40, X41, X42]:(((r3_lattice3(X38,X39,X40)|X39!=k16_lattice3(X38,X40)|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~v10_lattices(X38)|~v4_lattice3(X38)|~l3_lattices(X38)))&(~m1_subset_1(X41,u1_struct_0(X38))|(~r3_lattice3(X38,X41,X40)|r3_lattices(X38,X41,X39))|X39!=k16_lattice3(X38,X40)|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~v10_lattices(X38)|~v4_lattice3(X38)|~l3_lattices(X38))))&((m1_subset_1(esk6_3(X38,X39,X42),u1_struct_0(X38))|~r3_lattice3(X38,X39,X42)|X39=k16_lattice3(X38,X42)|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~v10_lattices(X38)|~v4_lattice3(X38)|~l3_lattices(X38)))&((r3_lattice3(X38,esk6_3(X38,X39,X42),X42)|~r3_lattice3(X38,X39,X42)|X39=k16_lattice3(X38,X42)|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~v10_lattices(X38)|~v4_lattice3(X38)|~l3_lattices(X38)))&(~r3_lattices(X38,esk6_3(X38,X39,X42),X39)|~r3_lattice3(X38,X39,X42)|X39=k16_lattice3(X38,X42)|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~v10_lattices(X38)|~v4_lattice3(X38)|~l3_lattices(X38)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 56.84/57.06  fof(c_0_13, plain, ![X17, X18, X19, X20]:(((r4_lattice3(X17,X19,X18)|X19!=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))&(~m1_subset_1(X20,u1_struct_0(X17))|(~r4_lattice3(X17,X20,X18)|r1_lattices(X17,X19,X20))|X19!=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17))))&((m1_subset_1(esk3_3(X17,X18,X19),u1_struct_0(X17))|~r4_lattice3(X17,X19,X18)|X19=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))&((r4_lattice3(X17,esk3_3(X17,X18,X19),X18)|~r4_lattice3(X17,X19,X18)|X19=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))&(~r1_lattices(X17,X19,esk3_3(X17,X18,X19))|~r4_lattice3(X17,X19,X18)|X19=k15_lattice3(X17,X18)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X17)|~v10_lattices(X17)|~v4_lattice3(X17)|~l3_lattices(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 56.84/57.06  fof(c_0_14, plain, ![X11, X12, X13, X14, X15]:((~r4_lattice3(X11,X12,X13)|(~m1_subset_1(X14,u1_struct_0(X11))|(~r2_hidden(X14,X13)|r1_lattices(X11,X14,X12)))|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&((m1_subset_1(esk2_3(X11,X12,X15),u1_struct_0(X11))|r4_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&((r2_hidden(esk2_3(X11,X12,X15),X15)|r4_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&(~r1_lattices(X11,esk2_3(X11,X12,X15),X12)|r4_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 56.84/57.06  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 56.84/57.06  cnf(c_0_16, plain, (v2_struct_0(X1)|m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 56.84/57.06  cnf(c_0_17, negated_conjecture, (l3_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 56.84/57.06  fof(c_0_18, plain, ![X32, X33, X34, X36, X37]:((((m1_subset_1(esk5_3(X32,X33,X34),u1_struct_0(X33))|~r2_hidden(X32,a_2_2_lattice3(X33,X34))|(v2_struct_0(X33)|~v10_lattices(X33)|~v4_lattice3(X33)|~l3_lattices(X33)))&(X32=esk5_3(X32,X33,X34)|~r2_hidden(X32,a_2_2_lattice3(X33,X34))|(v2_struct_0(X33)|~v10_lattices(X33)|~v4_lattice3(X33)|~l3_lattices(X33))))&(r4_lattice3(X33,esk5_3(X32,X33,X34),X34)|~r2_hidden(X32,a_2_2_lattice3(X33,X34))|(v2_struct_0(X33)|~v10_lattices(X33)|~v4_lattice3(X33)|~l3_lattices(X33))))&(~m1_subset_1(X37,u1_struct_0(X33))|X32!=X37|~r4_lattice3(X33,X37,X36)|r2_hidden(X32,a_2_2_lattice3(X33,X36))|(v2_struct_0(X33)|~v10_lattices(X33)|~v4_lattice3(X33)|~l3_lattices(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).
% 56.84/57.06  fof(c_0_19, plain, ![X5, X6, X7, X8, X9]:((~r3_lattice3(X5,X6,X7)|(~m1_subset_1(X8,u1_struct_0(X5))|(~r2_hidden(X8,X7)|r1_lattices(X5,X6,X8)))|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))&((m1_subset_1(esk1_3(X5,X6,X9),u1_struct_0(X5))|r3_lattice3(X5,X6,X9)|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))&((r2_hidden(esk1_3(X5,X6,X9),X9)|r3_lattice3(X5,X6,X9)|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))&(~r1_lattices(X5,X6,esk1_3(X5,X6,X9))|r3_lattice3(X5,X6,X9)|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l3_lattices(X5)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 56.84/57.06  cnf(c_0_20, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|X2!=k16_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 56.84/57.06  cnf(c_0_21, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 56.84/57.06  cnf(c_0_22, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 56.84/57.06  cnf(c_0_23, negated_conjecture, (m1_subset_1(k16_lattice3(esk7_0,X1),u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 56.84/57.06  cnf(c_0_24, plain, (r2_hidden(X3,a_2_2_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r4_lattice3(X2,X1,X4)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 56.84/57.06  cnf(c_0_25, plain, (r4_lattice3(X1,esk3_3(X1,X2,X3),X2)|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 56.84/57.06  cnf(c_0_26, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 56.84/57.06  cnf(c_0_27, plain, (r3_lattice3(X1,k16_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]), c_0_16])).
% 56.84/57.06  cnf(c_0_28, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_21])).
% 56.84/57.06  cnf(c_0_29, negated_conjecture, (r4_lattice3(esk7_0,k16_lattice3(esk7_0,X1),X2)|m1_subset_1(esk2_3(esk7_0,k16_lattice3(esk7_0,X1),X2),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_30, negated_conjecture, (v4_lattice3(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 56.84/57.06  cnf(c_0_31, negated_conjecture, (v10_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 56.84/57.06  cnf(c_0_32, plain, (r2_hidden(X1,a_2_2_lattice3(X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_24])).
% 56.84/57.06  cnf(c_0_33, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|r4_lattice3(X1,esk3_3(X1,X2,X3),X2)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_25])).
% 56.84/57.06  cnf(c_0_34, plain, (r1_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_16])).
% 56.84/57.06  cnf(c_0_35, negated_conjecture, (k16_lattice3(esk7_0,X1)=k15_lattice3(esk7_0,X2)|m1_subset_1(esk2_3(esk7_0,k16_lattice3(esk7_0,X1),X2),u1_struct_0(esk7_0))|m1_subset_1(esk3_3(esk7_0,X2,k16_lattice3(esk7_0,X1)),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_23]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_36, plain, (X1=k15_lattice3(X2,X3)|r2_hidden(esk3_3(X2,X3,X1),a_2_2_lattice3(X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_28])).
% 56.84/57.06  cnf(c_0_37, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X1)|X2!=k15_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 56.84/57.06  fof(c_0_38, plain, ![X22, X23]:(v2_struct_0(X22)|~l3_lattices(X22)|k16_lattice3(X22,X23)=k15_lattice3(X22,a_2_1_lattice3(X22,X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d22_lattice3])])])])).
% 56.84/57.06  cnf(c_0_39, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk3_3(X1,X3,X2))|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 56.84/57.06  cnf(c_0_40, negated_conjecture, (k16_lattice3(esk7_0,X1)=k15_lattice3(esk7_0,X2)|r1_lattices(esk7_0,k16_lattice3(esk7_0,X3),esk3_3(esk7_0,X2,k16_lattice3(esk7_0,X1)))|m1_subset_1(esk2_3(esk7_0,k16_lattice3(esk7_0,X1),X2),u1_struct_0(esk7_0))|~r2_hidden(esk3_3(esk7_0,X2,k16_lattice3(esk7_0,X1)),X3)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_30]), c_0_31]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_41, negated_conjecture, (k16_lattice3(esk7_0,X1)=k15_lattice3(esk7_0,X2)|r2_hidden(esk3_3(esk7_0,X2,k16_lattice3(esk7_0,X1)),a_2_2_lattice3(esk7_0,X2))|m1_subset_1(esk2_3(esk7_0,k16_lattice3(esk7_0,X1),X2),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_29]), c_0_30]), c_0_31]), c_0_23]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_42, plain, (v2_struct_0(X1)|r4_lattice3(X1,X2,X3)|X2!=k15_lattice3(X1,X3)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_37])).
% 56.84/57.06  cnf(c_0_43, plain, (v2_struct_0(X1)|k16_lattice3(X1,X2)=k15_lattice3(X1,a_2_1_lattice3(X1,X2))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 56.84/57.06  fof(c_0_44, plain, ![X26, X27, X28, X30, X31]:((((m1_subset_1(esk4_3(X26,X27,X28),u1_struct_0(X27))|~r2_hidden(X26,a_2_1_lattice3(X27,X28))|(v2_struct_0(X27)|~l3_lattices(X27)))&(X26=esk4_3(X26,X27,X28)|~r2_hidden(X26,a_2_1_lattice3(X27,X28))|(v2_struct_0(X27)|~l3_lattices(X27))))&(r3_lattice3(X27,esk4_3(X26,X27,X28),X28)|~r2_hidden(X26,a_2_1_lattice3(X27,X28))|(v2_struct_0(X27)|~l3_lattices(X27))))&(~m1_subset_1(X31,u1_struct_0(X27))|X26!=X31|~r3_lattice3(X27,X31,X30)|r2_hidden(X26,a_2_1_lattice3(X27,X30))|(v2_struct_0(X27)|~l3_lattices(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_lattice3])])])])])])])).
% 56.84/57.06  cnf(c_0_45, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~r1_lattices(X1,X2,esk3_3(X1,X3,X2))), inference(cn,[status(thm)],[c_0_39])).
% 56.84/57.06  cnf(c_0_46, negated_conjecture, (k16_lattice3(esk7_0,X1)=k15_lattice3(esk7_0,X2)|r1_lattices(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X2)),esk3_3(esk7_0,X2,k16_lattice3(esk7_0,X1)))|m1_subset_1(esk2_3(esk7_0,k16_lattice3(esk7_0,X1),X2),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 56.84/57.06  cnf(c_0_47, plain, (r4_lattice3(X1,k15_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_42])).
% 56.84/57.06  cnf(c_0_48, negated_conjecture, (k15_lattice3(esk7_0,a_2_1_lattice3(esk7_0,X1))=k16_lattice3(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_43]), c_0_17])])).
% 56.84/57.06  cnf(c_0_49, plain, (r2_hidden(X3,a_2_1_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r3_lattice3(X2,X1,X4)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 56.84/57.06  cnf(c_0_50, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 56.84/57.06  cnf(c_0_51, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|m1_subset_1(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),u1_struct_0(esk7_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_30]), c_0_31]), c_0_23]), c_0_17])]), c_0_15]), c_0_29])).
% 56.84/57.06  cnf(c_0_52, plain, (r1_lattices(X1,X4,X2)|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 56.84/57.06  cnf(c_0_53, negated_conjecture, (r4_lattice3(esk7_0,k16_lattice3(esk7_0,X1),a_2_1_lattice3(esk7_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_30]), c_0_31]), c_0_23]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_54, plain, (r2_hidden(X1,a_2_1_lattice3(X2,X3))|v2_struct_0(X2)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_49])).
% 56.84/57.06  cnf(c_0_55, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r2_hidden(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),X2),X2)|r3_lattice3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_56, negated_conjecture, (r1_lattices(esk7_0,X1,k16_lattice3(esk7_0,X2))|~r2_hidden(X1,a_2_1_lattice3(esk7_0,X2))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_23]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_57, plain, (X1=esk5_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 56.84/57.06  cnf(c_0_58, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r2_hidden(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),X2),X2)|r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,X2))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_17])]), c_0_15]), c_0_51])).
% 56.84/57.06  cnf(c_0_59, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r1_lattices(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),k16_lattice3(esk7_0,X2))|~r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,X2))), inference(spm,[status(thm)],[c_0_56, c_0_51])).
% 56.84/57.06  cnf(c_0_60, negated_conjecture, (esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(X2,X3)),X2,X3)=esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(X2,X3))|k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,a_2_2_lattice3(X2,X3)))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 56.84/57.06  cnf(c_0_61, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk2_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 56.84/57.06  cnf(c_0_62, negated_conjecture, (esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(X2,X3)),X2,X3)=esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(X2,X3))|k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r1_lattices(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),k16_lattice3(esk7_0,a_2_2_lattice3(X2,X3)))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 56.84/57.06  cnf(c_0_63, negated_conjecture, (esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)),esk7_0,X1)=esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1))|k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r4_lattice3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_23]), c_0_17]), c_0_30]), c_0_31])]), c_0_15])).
% 56.84/57.06  cnf(c_0_64, negated_conjecture, (esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)),esk7_0,X1)=esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1))|k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|m1_subset_1(esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_63]), c_0_30]), c_0_31]), c_0_23]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_65, negated_conjecture, (esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)),esk7_0,X1)=esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1))|k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r1_lattices(esk7_0,k16_lattice3(esk7_0,X2),esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))))|~r2_hidden(esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_64]), c_0_30]), c_0_31]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_66, negated_conjecture, (esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)),esk7_0,X1)=esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1))|k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r2_hidden(esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))),a_2_2_lattice3(esk7_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_63]), c_0_30]), c_0_31]), c_0_23]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_67, plain, (r4_lattice3(X1,esk5_3(X2,X1,X3),X3)|v2_struct_0(X1)|~r2_hidden(X2,a_2_2_lattice3(X1,X3))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 56.84/57.06  cnf(c_0_68, negated_conjecture, (esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)),esk7_0,X1)=esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1))|k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r1_lattices(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 56.84/57.06  cnf(c_0_69, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 56.84/57.06  cnf(c_0_70, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r4_lattice3(X2,esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(X2,X3)),X2,X3),X3)|r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,a_2_2_lattice3(X2,X3)))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_67, c_0_58])).
% 56.84/57.06  cnf(c_0_71, negated_conjecture, (esk5_3(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)),esk7_0,X1)=esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1))|k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_68]), c_0_30]), c_0_31]), c_0_23]), c_0_17])]), c_0_15]), c_0_63])).
% 56.84/57.06  cnf(c_0_72, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r3_lattice3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),X2)|m1_subset_1(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),X2),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_51]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_73, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r4_lattice3(esk7_0,esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)),X1)|r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_30]), c_0_31]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_74, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,X2))|m1_subset_1(esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),X2),u1_struct_0(esk7_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_72]), c_0_17])]), c_0_15]), c_0_51])).
% 56.84/57.06  cnf(c_0_75, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 56.84/57.06  cnf(c_0_76, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r1_lattices(esk7_0,X2,esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)))|r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)))|~r2_hidden(X2,X1)|~m1_subset_1(X2,u1_struct_0(esk7_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_73]), c_0_17])]), c_0_15]), c_0_74])).
% 56.84/57.06  cnf(c_0_77, negated_conjecture, (r4_lattice3(esk7_0,k16_lattice3(esk7_0,X1),X2)|r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,X1),X2),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_23]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_78, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X2))=k15_lattice3(esk7_0,X2)|r1_lattices(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X2)),X2),a_2_2_lattice3(esk7_0,X2)))|r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X2)),X2),a_2_1_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X2)))|~r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),X2)), inference(spm,[status(thm)],[c_0_76, c_0_51])).
% 56.84/57.06  cnf(c_0_79, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,X1),X2),X2)|r2_hidden(k16_lattice3(esk7_0,X1),a_2_2_lattice3(esk7_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_77]), c_0_30]), c_0_31]), c_0_23]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_80, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk1_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 56.84/57.06  cnf(c_0_81, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r1_lattices(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),esk1_3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1)))|r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)))|r2_hidden(k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),a_2_2_lattice3(esk7_0,X1))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 56.84/57.06  cnf(c_0_82, negated_conjecture, (r2_hidden(k16_lattice3(esk7_0,X1),a_2_2_lattice3(esk7_0,X2))|m1_subset_1(esk2_3(esk7_0,k16_lattice3(esk7_0,X1),X2),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_29]), c_0_30]), c_0_31]), c_0_23]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_83, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)))|r2_hidden(k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),a_2_2_lattice3(esk7_0,X1))|r3_lattice3(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_2_lattice3(esk7_0,X1))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_17])]), c_0_15]), c_0_82])).
% 56.84/57.06  cnf(c_0_84, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r2_hidden(esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),a_2_1_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)))|r2_hidden(k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),a_2_2_lattice3(esk7_0,X1))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_83]), c_0_17])]), c_0_15]), c_0_82])).
% 56.84/57.06  cnf(c_0_85, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r1_lattices(esk7_0,esk2_3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1),k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)))|r2_hidden(k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),a_2_2_lattice3(esk7_0,X1))), inference(spm,[status(thm)],[c_0_59, c_0_84])).
% 56.84/57.06  cnf(c_0_86, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r4_lattice3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1)|r2_hidden(k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),a_2_2_lattice3(esk7_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_85]), c_0_23]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_87, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r2_hidden(k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),a_2_2_lattice3(esk7_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_86]), c_0_30]), c_0_31]), c_0_23]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_88, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r4_lattice3(esk7_0,esk5_3(k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),esk7_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_87]), c_0_30]), c_0_31]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_89, negated_conjecture, (esk5_3(k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),esk7_0,X1)=k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))|k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_87]), c_0_30]), c_0_31]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_90, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r4_lattice3(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),X1)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 56.84/57.06  cnf(c_0_91, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|m1_subset_1(esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_90]), c_0_30]), c_0_31]), c_0_23]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_92, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r1_lattices(esk7_0,k16_lattice3(esk7_0,X2),esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))))|~r2_hidden(esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_91]), c_0_30]), c_0_31]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_93, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r2_hidden(esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))),a_2_2_lattice3(esk7_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_90]), c_0_30]), c_0_31]), c_0_23]), c_0_17])]), c_0_15])).
% 56.84/57.06  cnf(c_0_94, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)|r1_lattices(esk7_0,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1)),esk3_3(esk7_0,X1,k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 56.84/57.06  cnf(c_0_95, negated_conjecture, (k15_lattice3(esk7_0,esk8_0)!=k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 56.84/57.06  cnf(c_0_96, negated_conjecture, (k16_lattice3(esk7_0,a_2_2_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_94]), c_0_30]), c_0_31]), c_0_23]), c_0_17])]), c_0_15]), c_0_90])).
% 56.84/57.06  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96])]), ['proof']).
% 56.84/57.06  # SZS output end CNFRefutation
% 56.84/57.06  # Proof object total steps             : 98
% 56.84/57.06  # Proof object clause steps            : 79
% 56.84/57.06  # Proof object formula steps           : 19
% 56.84/57.06  # Proof object conjectures             : 53
% 56.84/57.06  # Proof object clause conjectures      : 50
% 56.84/57.06  # Proof object formula conjectures     : 3
% 56.84/57.06  # Proof object initial clauses used    : 24
% 56.84/57.06  # Proof object initial formulas used   : 9
% 56.84/57.06  # Proof object generating inferences   : 46
% 56.84/57.06  # Proof object simplifying inferences  : 174
% 56.84/57.06  # Training examples: 0 positive, 0 negative
% 56.84/57.06  # Parsed axioms                        : 9
% 56.84/57.06  # Removed by relevancy pruning/SinE    : 0
% 56.84/57.06  # Initial clauses                      : 33
% 56.84/57.06  # Removed in clause preprocessing      : 0
% 56.84/57.06  # Initial clauses in saturation        : 33
% 56.84/57.06  # Processed clauses                    : 37683
% 56.84/57.06  # ...of these trivial                  : 1
% 56.84/57.06  # ...subsumed                          : 15275
% 56.84/57.06  # ...remaining for further processing  : 22407
% 56.84/57.06  # Other redundant clauses eliminated   : 6
% 56.84/57.06  # Clauses deleted for lack of memory   : 119364
% 56.84/57.06  # Backward-subsumed                    : 1689
% 56.84/57.06  # Backward-rewritten                   : 2861
% 56.84/57.06  # Generated clauses                    : 2929216
% 56.84/57.06  # ...of the previous two non-trivial   : 2900134
% 56.84/57.06  # Contextual simplify-reflections      : 2689
% 56.84/57.06  # Paramodulations                      : 2929208
% 56.84/57.06  # Factorizations                       : 2
% 56.84/57.06  # Equation resolutions                 : 6
% 56.84/57.06  # Propositional unsat checks           : 0
% 56.84/57.06  #    Propositional check models        : 0
% 56.84/57.06  #    Propositional check unsatisfiable : 0
% 56.84/57.06  #    Propositional clauses             : 0
% 56.84/57.06  #    Propositional clauses after purity: 0
% 56.84/57.06  #    Propositional unsat core size     : 0
% 56.84/57.06  #    Propositional preprocessing time  : 0.000
% 56.84/57.06  #    Propositional encoding time       : 0.000
% 56.84/57.06  #    Propositional solver time         : 0.000
% 56.84/57.06  #    Success case prop preproc time    : 0.000
% 56.84/57.06  #    Success case prop encoding time   : 0.000
% 56.84/57.06  #    Success case prop solver time     : 0.000
% 56.84/57.06  # Current number of processed clauses  : 17818
% 56.84/57.06  #    Positive orientable unit clauses  : 19
% 56.84/57.06  #    Positive unorientable unit clauses: 0
% 56.84/57.06  #    Negative unit clauses             : 1
% 56.84/57.06  #    Non-unit-clauses                  : 17798
% 56.84/57.06  # Current number of unprocessed clauses: 1827130
% 56.84/57.06  # ...number of literals in the above   : 11716246
% 56.84/57.06  # Current number of archived formulas  : 0
% 56.84/57.06  # Current number of archived clauses   : 4583
% 56.84/57.06  # Clause-clause subsumption calls (NU) : 52386497
% 56.84/57.06  # Rec. Clause-clause subsumption calls : 1014682
% 56.84/57.06  # Non-unit clause-clause subsumptions  : 19653
% 56.84/57.06  # Unit Clause-clause subsumption calls : 21698
% 56.84/57.06  # Rewrite failures with RHS unbound    : 0
% 56.84/57.06  # BW rewrite match attempts            : 131
% 56.84/57.06  # BW rewrite match successes           : 36
% 56.84/57.06  # Condensation attempts                : 0
% 56.84/57.06  # Condensation successes               : 0
% 56.84/57.06  # Termbank termtop insertions          : 187173486
% 56.96/57.16  
% 56.96/57.16  # -------------------------------------------------
% 56.96/57.16  # User time                : 55.720 s
% 56.96/57.16  # System time              : 1.061 s
% 56.96/57.16  # Total time               : 56.781 s
% 56.96/57.16  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
