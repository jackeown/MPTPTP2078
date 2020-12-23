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
% DateTime   : Thu Dec  3 11:15:05 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 293 expanded)
%              Number of clauses        :   55 ( 114 expanded)
%              Number of leaves         :    9 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          :  488 (2234 expanded)
%              Number of equality atoms :   17 (  83 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   40 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t46_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => ( r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
            & r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_lattice3)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(dt_k16_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

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

fof(t37_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] : k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattice3)).

fof(c_0_9,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( ( ~ r4_lattice3(X17,X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r2_hidden(X20,X19)
        | r1_lattices(X17,X20,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ l3_lattices(X17) )
      & ( m1_subset_1(esk3_3(X17,X18,X21),u1_struct_0(X17))
        | r4_lattice3(X17,X18,X21)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ l3_lattices(X17) )
      & ( r2_hidden(esk3_3(X17,X18,X21),X21)
        | r4_lattice3(X17,X18,X21)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ l3_lattices(X17) )
      & ( ~ r1_lattices(X17,esk3_3(X17,X18,X21),X18)
        | r4_lattice3(X17,X18,X21)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ l3_lattices(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

fof(c_0_10,plain,(
    ! [X27,X28,X29,X31,X32] :
      ( ( m1_subset_1(esk4_3(X27,X28,X29),u1_struct_0(X28))
        | ~ r2_hidden(X27,a_2_2_lattice3(X28,X29))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28) )
      & ( X27 = esk4_3(X27,X28,X29)
        | ~ r2_hidden(X27,a_2_2_lattice3(X28,X29))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28) )
      & ( r4_lattice3(X28,esk4_3(X27,X28,X29),X29)
        | ~ r2_hidden(X27,a_2_2_lattice3(X28,X29))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28) )
      & ( ~ m1_subset_1(X32,u1_struct_0(X28))
        | X27 != X32
        | ~ r4_lattice3(X28,X32,X31)
        | r2_hidden(X27,a_2_2_lattice3(X28,X31))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).

cnf(c_0_11,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( r4_lattice3(X1,esk4_3(X2,X1,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_2_lattice3(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2,X3] :
            ( r1_tarski(X2,X3)
           => ( r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
              & r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t46_lattice3])).

cnf(c_0_15,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk3_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r1_lattices(X1,X2,esk4_3(X3,X1,X4))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X3,a_2_2_lattice3(X1,X4))
    | ~ r2_hidden(X2,X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

fof(c_0_17,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v10_lattices(esk6_0)
    & v4_lattice3(esk6_0)
    & l3_lattices(esk6_0)
    & r1_tarski(esk7_0,esk8_0)
    & ( ~ r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0))
      | ~ r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_19,plain,(
    ! [X33,X34,X35,X36,X37] :
      ( ( r3_lattice3(X33,X34,X35)
        | X34 != k16_lattice3(X33,X35)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ v4_lattice3(X33)
        | ~ l3_lattices(X33) )
      & ( ~ m1_subset_1(X36,u1_struct_0(X33))
        | ~ r3_lattice3(X33,X36,X35)
        | r3_lattices(X33,X36,X34)
        | X34 != k16_lattice3(X33,X35)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ v4_lattice3(X33)
        | ~ l3_lattices(X33) )
      & ( m1_subset_1(esk5_3(X33,X34,X37),u1_struct_0(X33))
        | ~ r3_lattice3(X33,X34,X37)
        | X34 = k16_lattice3(X33,X37)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ v4_lattice3(X33)
        | ~ l3_lattices(X33) )
      & ( r3_lattice3(X33,esk5_3(X33,X34,X37),X37)
        | ~ r3_lattice3(X33,X34,X37)
        | X34 = k16_lattice3(X33,X37)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ v4_lattice3(X33)
        | ~ l3_lattices(X33) )
      & ( ~ r3_lattices(X33,esk5_3(X33,X34,X37),X34)
        | ~ r3_lattice3(X33,X34,X37)
        | X34 = k16_lattice3(X33,X37)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ v4_lattice3(X33)
        | ~ l3_lattices(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

fof(c_0_20,plain,(
    ! [X25,X26] :
      ( v2_struct_0(X25)
      | ~ l3_lattices(X25)
      | m1_subset_1(k16_lattice3(X25,X26),u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

cnf(c_0_21,plain,
    ( r4_lattice3(X1,esk4_3(X2,X1,X3),X4)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(esk3_3(X1,esk4_3(X2,X1,X3),X4),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk3_3(X1,esk4_3(X2,X1,X3),X4),X3)
    | ~ r2_hidden(X2,a_2_2_lattice3(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_13])).

cnf(c_0_22,plain,
    ( X1 = esk4_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r3_lattice3(X11,X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r2_hidden(X14,X13)
        | r1_lattices(X11,X12,X14)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l3_lattices(X11) )
      & ( m1_subset_1(esk2_3(X11,X12,X15),u1_struct_0(X11))
        | r3_lattice3(X11,X12,X15)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l3_lattices(X11) )
      & ( r2_hidden(esk2_3(X11,X12,X15),X15)
        | r3_lattice3(X11,X12,X15)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l3_lattices(X11) )
      & ( ~ r1_lattices(X11,X12,esk2_3(X11,X12,X15))
        | r3_lattice3(X11,X12,X15)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l3_lattices(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

cnf(c_0_26,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k16_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X4)
    | ~ r2_hidden(X2,a_2_2_lattice3(X1,X4)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r3_lattice3(X1,k16_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk3_3(X1,X2,X3),esk7_0)
    | ~ r2_hidden(X2,a_2_2_lattice3(X1,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_22])).

cnf(c_0_35,plain,
    ( r2_hidden(X3,a_2_2_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r4_lattice3(X2,X1,X4)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk2_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( r1_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( r4_lattice3(X1,X2,esk7_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(esk3_3(X1,X2,esk7_0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X2,a_2_2_lattice3(X1,esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_39,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_2_lattice3(X1,X3))
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( r3_lattice3(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(esk2_3(X1,k16_lattice3(X1,X2),X3),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk2_3(X1,k16_lattice3(X1,X2),X3),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( r4_lattice3(X1,X2,esk7_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X2,a_2_2_lattice3(X1,esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_34])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk4_3(X2,X1,X3),a_2_2_lattice3(X1,X3))
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X2,a_2_2_lattice3(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_12]),c_0_13])).

fof(c_0_44,plain,(
    ! [X39,X40] :
      ( v2_struct_0(X39)
      | ~ v10_lattices(X39)
      | ~ v4_lattice3(X39)
      | ~ l3_lattices(X39)
      | k15_lattice3(X39,X40) = k16_lattice3(X39,a_2_2_lattice3(X39,X40)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).

cnf(c_0_45,negated_conjecture,
    ( r3_lattice3(X1,k16_lattice3(X1,esk8_0),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(esk2_3(X1,k16_lattice3(X1,esk8_0),X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk2_3(X1,k16_lattice3(X1,esk8_0),X2),esk7_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_29])).

cnf(c_0_46,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_47,negated_conjecture,
    ( r4_lattice3(X1,esk4_3(X2,X1,esk8_0),esk7_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X2,a_2_2_lattice3(X1,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( ~ r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0))
    | ~ r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( v4_lattice3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( v10_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_52,negated_conjecture,
    ( l3_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_54,negated_conjecture,
    ( r3_lattice3(X1,k16_lattice3(X1,esk8_0),esk7_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(esk2_3(X1,k16_lattice3(X1,esk8_0),esk7_0),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_27])).

cnf(c_0_55,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_56,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk4_3(X2,X1,esk8_0),a_2_2_lattice3(X1,esk7_0))
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X2,a_2_2_lattice3(X1,esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_47]),c_0_13])).

cnf(c_0_57,negated_conjecture,
    ( ~ r3_lattices(esk6_0,k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,esk7_0)),k15_lattice3(esk6_0,esk8_0))
    | ~ r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_52])]),c_0_53])).

cnf(c_0_58,plain,
    ( r3_lattices(X2,X1,X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_lattice3(X2,X1,X3)
    | X4 != k16_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( r3_lattice3(X1,k16_lattice3(X1,esk8_0),esk7_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_27])).

cnf(c_0_60,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_2_lattice3(X1,esk7_0))
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X2,a_2_2_lattice3(X1,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( ~ r3_lattices(esk6_0,k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,esk7_0)),k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,esk8_0)))
    | ~ r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_49]),c_0_50]),c_0_51]),c_0_52])]),c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( r3_lattices(X1,k16_lattice3(X1,esk8_0),X2)
    | v2_struct_0(X1)
    | X2 != k16_lattice3(X1,esk7_0)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_27])).

fof(c_0_63,plain,(
    ! [X41,X42,X43] :
      ( v2_struct_0(X41)
      | ~ v10_lattices(X41)
      | ~ v4_lattice3(X41)
      | ~ l3_lattices(X41)
      | ~ m1_subset_1(X42,u1_struct_0(X41))
      | ~ r3_lattice3(X41,X42,X43)
      | r3_lattices(X41,X42,k16_lattice3(X41,X43)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_lattice3])])])])).

cnf(c_0_64,negated_conjecture,
    ( r3_lattice3(X1,X2,a_2_2_lattice3(X3,esk8_0))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | r2_hidden(esk2_3(X1,X2,a_2_2_lattice3(X3,esk8_0)),a_2_2_lattice3(X3,esk7_0))
    | ~ v4_lattice3(X3)
    | ~ v10_lattices(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_46])).

cnf(c_0_65,negated_conjecture,
    ( ~ r3_lattices(esk6_0,k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,esk7_0)),k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,esk8_0)))
    | ~ m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_50]),c_0_51]),c_0_52])]),c_0_53])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,X2,k16_lattice3(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r3_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r3_lattice3(X1,k16_lattice3(X1,a_2_2_lattice3(X2,esk7_0)),a_2_2_lattice3(X2,esk8_0))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ m1_subset_1(esk2_3(X1,k16_lattice3(X1,a_2_2_lattice3(X2,esk7_0)),a_2_2_lattice3(X2,esk8_0)),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_64]),c_0_27])).

cnf(c_0_68,plain,
    ( r3_lattice3(X1,X2,a_2_2_lattice3(X3,X4))
    | m1_subset_1(esk2_3(X1,X2,a_2_2_lattice3(X3,X4)),u1_struct_0(X3))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v4_lattice3(X3)
    | ~ v10_lattices(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_46])).

cnf(c_0_69,negated_conjecture,
    ( ~ r3_lattice3(esk6_0,k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,esk7_0)),a_2_2_lattice3(esk6_0,esk8_0))
    | ~ m1_subset_1(k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | ~ m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_50]),c_0_51]),c_0_52])]),c_0_53])).

cnf(c_0_70,negated_conjecture,
    ( r3_lattice3(X1,k16_lattice3(X1,a_2_2_lattice3(X1,esk7_0)),a_2_2_lattice3(X1,esk8_0))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_27])).

cnf(c_0_71,negated_conjecture,
    ( ~ m1_subset_1(k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | ~ m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_50]),c_0_51]),c_0_52])]),c_0_53])).

cnf(c_0_72,negated_conjecture,
    ( ~ m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_27]),c_0_52])]),c_0_53])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_27]),c_0_52])]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n013.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 11:39:24 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.17/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.17/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.17/0.38  #
% 0.17/0.38  # Preprocessing time       : 0.030 s
% 0.17/0.38  # Presaturation interreduction done
% 0.17/0.38  
% 0.17/0.38  # Proof found!
% 0.17/0.38  # SZS status Theorem
% 0.17/0.38  # SZS output start CNFRefutation
% 0.17/0.38  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 0.17/0.38  fof(fraenkel_a_2_2_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_2_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r4_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 0.17/0.38  fof(t46_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_lattice3)).
% 0.17/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.17/0.38  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 0.17/0.38  fof(dt_k16_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 0.17/0.38  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 0.17/0.38  fof(t37_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_lattice3)).
% 0.17/0.38  fof(t40_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)=>r3_lattices(X1,X2,k16_lattice3(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_lattice3)).
% 0.17/0.38  fof(c_0_9, plain, ![X17, X18, X19, X20, X21]:((~r4_lattice3(X17,X18,X19)|(~m1_subset_1(X20,u1_struct_0(X17))|(~r2_hidden(X20,X19)|r1_lattices(X17,X20,X18)))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))&((m1_subset_1(esk3_3(X17,X18,X21),u1_struct_0(X17))|r4_lattice3(X17,X18,X21)|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))&((r2_hidden(esk3_3(X17,X18,X21),X21)|r4_lattice3(X17,X18,X21)|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))&(~r1_lattices(X17,esk3_3(X17,X18,X21),X18)|r4_lattice3(X17,X18,X21)|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~l3_lattices(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.17/0.38  fof(c_0_10, plain, ![X27, X28, X29, X31, X32]:((((m1_subset_1(esk4_3(X27,X28,X29),u1_struct_0(X28))|~r2_hidden(X27,a_2_2_lattice3(X28,X29))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28)))&(X27=esk4_3(X27,X28,X29)|~r2_hidden(X27,a_2_2_lattice3(X28,X29))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28))))&(r4_lattice3(X28,esk4_3(X27,X28,X29),X29)|~r2_hidden(X27,a_2_2_lattice3(X28,X29))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28))))&(~m1_subset_1(X32,u1_struct_0(X28))|X27!=X32|~r4_lattice3(X28,X32,X31)|r2_hidden(X27,a_2_2_lattice3(X28,X31))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).
% 0.17/0.38  cnf(c_0_11, plain, (r1_lattices(X1,X4,X2)|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.17/0.38  cnf(c_0_12, plain, (r4_lattice3(X1,esk4_3(X2,X1,X3),X3)|v2_struct_0(X1)|~r2_hidden(X2,a_2_2_lattice3(X1,X3))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.38  cnf(c_0_13, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.38  fof(c_0_14, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2)))))), inference(assume_negation,[status(cth)],[t46_lattice3])).
% 0.17/0.38  cnf(c_0_15, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk3_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.17/0.38  cnf(c_0_16, plain, (r1_lattices(X1,X2,esk4_3(X3,X1,X4))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)|~r2_hidden(X3,a_2_2_lattice3(X1,X4))|~r2_hidden(X2,X4)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 0.17/0.38  fof(c_0_17, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.17/0.38  fof(c_0_18, negated_conjecture, ((((~v2_struct_0(esk6_0)&v10_lattices(esk6_0))&v4_lattice3(esk6_0))&l3_lattices(esk6_0))&(r1_tarski(esk7_0,esk8_0)&(~r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0))|~r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.17/0.38  fof(c_0_19, plain, ![X33, X34, X35, X36, X37]:(((r3_lattice3(X33,X34,X35)|X34!=k16_lattice3(X33,X35)|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v10_lattices(X33)|~v4_lattice3(X33)|~l3_lattices(X33)))&(~m1_subset_1(X36,u1_struct_0(X33))|(~r3_lattice3(X33,X36,X35)|r3_lattices(X33,X36,X34))|X34!=k16_lattice3(X33,X35)|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v10_lattices(X33)|~v4_lattice3(X33)|~l3_lattices(X33))))&((m1_subset_1(esk5_3(X33,X34,X37),u1_struct_0(X33))|~r3_lattice3(X33,X34,X37)|X34=k16_lattice3(X33,X37)|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v10_lattices(X33)|~v4_lattice3(X33)|~l3_lattices(X33)))&((r3_lattice3(X33,esk5_3(X33,X34,X37),X37)|~r3_lattice3(X33,X34,X37)|X34=k16_lattice3(X33,X37)|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v10_lattices(X33)|~v4_lattice3(X33)|~l3_lattices(X33)))&(~r3_lattices(X33,esk5_3(X33,X34,X37),X34)|~r3_lattice3(X33,X34,X37)|X34=k16_lattice3(X33,X37)|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v10_lattices(X33)|~v4_lattice3(X33)|~l3_lattices(X33)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.17/0.38  fof(c_0_20, plain, ![X25, X26]:(v2_struct_0(X25)|~l3_lattices(X25)|m1_subset_1(k16_lattice3(X25,X26),u1_struct_0(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).
% 0.17/0.38  cnf(c_0_21, plain, (r4_lattice3(X1,esk4_3(X2,X1,X3),X4)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~m1_subset_1(esk3_3(X1,esk4_3(X2,X1,X3),X4),u1_struct_0(X1))|~l3_lattices(X1)|~r2_hidden(esk3_3(X1,esk4_3(X2,X1,X3),X4),X3)|~r2_hidden(X2,a_2_2_lattice3(X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_13])).
% 0.17/0.38  cnf(c_0_22, plain, (X1=esk4_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.38  cnf(c_0_23, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.17/0.38  cnf(c_0_24, negated_conjecture, (r1_tarski(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.17/0.38  fof(c_0_25, plain, ![X11, X12, X13, X14, X15]:((~r3_lattice3(X11,X12,X13)|(~m1_subset_1(X14,u1_struct_0(X11))|(~r2_hidden(X14,X13)|r1_lattices(X11,X12,X14)))|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&((m1_subset_1(esk2_3(X11,X12,X15),u1_struct_0(X11))|r3_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&((r2_hidden(esk2_3(X11,X12,X15),X15)|r3_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))&(~r1_lattices(X11,X12,esk2_3(X11,X12,X15))|r3_lattice3(X11,X12,X15)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l3_lattices(X11)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.17/0.38  cnf(c_0_26, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|X2!=k16_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.38  cnf(c_0_27, plain, (v2_struct_0(X1)|m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.38  cnf(c_0_28, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|~l3_lattices(X1)|~r2_hidden(esk3_3(X1,X2,X3),X4)|~r2_hidden(X2,a_2_2_lattice3(X1,X4))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.17/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.17/0.38  cnf(c_0_30, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.38  cnf(c_0_31, plain, (r3_lattice3(X1,k16_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_26]), c_0_27])).
% 0.17/0.38  cnf(c_0_32, negated_conjecture, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|~l3_lattices(X1)|~r2_hidden(esk3_3(X1,X2,X3),esk7_0)|~r2_hidden(X2,a_2_2_lattice3(X1,esk8_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.17/0.38  cnf(c_0_33, plain, (r2_hidden(esk3_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.17/0.38  cnf(c_0_34, plain, (m1_subset_1(X1,u1_struct_0(X2))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)|~r2_hidden(X1,a_2_2_lattice3(X2,X3))), inference(spm,[status(thm)],[c_0_13, c_0_22])).
% 0.17/0.38  cnf(c_0_35, plain, (r2_hidden(X3,a_2_2_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r4_lattice3(X2,X1,X4)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.38  cnf(c_0_36, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk2_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.38  cnf(c_0_37, plain, (r1_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_27])).
% 0.17/0.38  cnf(c_0_38, negated_conjecture, (r4_lattice3(X1,X2,esk7_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~m1_subset_1(esk3_3(X1,X2,esk7_0),u1_struct_0(X1))|~l3_lattices(X1)|~r2_hidden(X2,a_2_2_lattice3(X1,esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.17/0.38  cnf(c_0_39, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.17/0.38  cnf(c_0_40, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_2_lattice3(X1,X3))|~v4_lattice3(X1)|~v10_lattices(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_35])).
% 0.17/0.38  cnf(c_0_41, plain, (r3_lattice3(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~m1_subset_1(esk2_3(X1,k16_lattice3(X1,X2),X3),u1_struct_0(X1))|~l3_lattices(X1)|~r2_hidden(esk2_3(X1,k16_lattice3(X1,X2),X3),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_27])).
% 0.17/0.38  cnf(c_0_42, negated_conjecture, (r4_lattice3(X1,X2,esk7_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X2,a_2_2_lattice3(X1,esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_34])).
% 0.17/0.38  cnf(c_0_43, plain, (v2_struct_0(X1)|r2_hidden(esk4_3(X2,X1,X3),a_2_2_lattice3(X1,X3))|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X2,a_2_2_lattice3(X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_12]), c_0_13])).
% 0.17/0.38  fof(c_0_44, plain, ![X39, X40]:(v2_struct_0(X39)|~v10_lattices(X39)|~v4_lattice3(X39)|~l3_lattices(X39)|k15_lattice3(X39,X40)=k16_lattice3(X39,a_2_2_lattice3(X39,X40))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).
% 0.17/0.38  cnf(c_0_45, negated_conjecture, (r3_lattice3(X1,k16_lattice3(X1,esk8_0),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~m1_subset_1(esk2_3(X1,k16_lattice3(X1,esk8_0),X2),u1_struct_0(X1))|~l3_lattices(X1)|~r2_hidden(esk2_3(X1,k16_lattice3(X1,esk8_0),X2),esk7_0)), inference(spm,[status(thm)],[c_0_41, c_0_29])).
% 0.17/0.38  cnf(c_0_46, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.38  cnf(c_0_47, negated_conjecture, (r4_lattice3(X1,esk4_3(X2,X1,esk8_0),esk7_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X2,a_2_2_lattice3(X1,esk8_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.17/0.38  cnf(c_0_48, negated_conjecture, (~r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0))|~r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.17/0.38  cnf(c_0_49, plain, (v2_struct_0(X1)|k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.17/0.38  cnf(c_0_50, negated_conjecture, (v4_lattice3(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.17/0.38  cnf(c_0_51, negated_conjecture, (v10_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.17/0.38  cnf(c_0_52, negated_conjecture, (l3_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.17/0.38  cnf(c_0_53, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.17/0.38  cnf(c_0_54, negated_conjecture, (r3_lattice3(X1,k16_lattice3(X1,esk8_0),esk7_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~m1_subset_1(esk2_3(X1,k16_lattice3(X1,esk8_0),esk7_0),u1_struct_0(X1))|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_27])).
% 0.17/0.38  cnf(c_0_55, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.38  cnf(c_0_56, negated_conjecture, (v2_struct_0(X1)|r2_hidden(esk4_3(X2,X1,esk8_0),a_2_2_lattice3(X1,esk7_0))|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X2,a_2_2_lattice3(X1,esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_47]), c_0_13])).
% 0.17/0.38  cnf(c_0_57, negated_conjecture, (~r3_lattices(esk6_0,k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,esk7_0)),k15_lattice3(esk6_0,esk8_0))|~r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51]), c_0_52])]), c_0_53])).
% 0.17/0.38  cnf(c_0_58, plain, (r3_lattices(X2,X1,X4)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_lattice3(X2,X1,X3)|X4!=k16_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.38  cnf(c_0_59, negated_conjecture, (r3_lattice3(X1,k16_lattice3(X1,esk8_0),esk7_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_27])).
% 0.17/0.38  cnf(c_0_60, negated_conjecture, (v2_struct_0(X1)|r2_hidden(X2,a_2_2_lattice3(X1,esk7_0))|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X2,a_2_2_lattice3(X1,esk8_0))), inference(spm,[status(thm)],[c_0_56, c_0_22])).
% 0.17/0.38  cnf(c_0_61, negated_conjecture, (~r3_lattices(esk6_0,k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,esk7_0)),k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,esk8_0)))|~r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_49]), c_0_50]), c_0_51]), c_0_52])]), c_0_53])).
% 0.17/0.38  cnf(c_0_62, negated_conjecture, (r3_lattices(X1,k16_lattice3(X1,esk8_0),X2)|v2_struct_0(X1)|X2!=k16_lattice3(X1,esk7_0)|~v4_lattice3(X1)|~v10_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_27])).
% 0.17/0.38  fof(c_0_63, plain, ![X41, X42, X43]:(v2_struct_0(X41)|~v10_lattices(X41)|~v4_lattice3(X41)|~l3_lattices(X41)|(~m1_subset_1(X42,u1_struct_0(X41))|(~r3_lattice3(X41,X42,X43)|r3_lattices(X41,X42,k16_lattice3(X41,X43))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_lattice3])])])])).
% 0.17/0.38  cnf(c_0_64, negated_conjecture, (r3_lattice3(X1,X2,a_2_2_lattice3(X3,esk8_0))|v2_struct_0(X1)|v2_struct_0(X3)|r2_hidden(esk2_3(X1,X2,a_2_2_lattice3(X3,esk8_0)),a_2_2_lattice3(X3,esk7_0))|~v4_lattice3(X3)|~v10_lattices(X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X3)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_60, c_0_46])).
% 0.17/0.38  cnf(c_0_65, negated_conjecture, (~r3_lattices(esk6_0,k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,esk7_0)),k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,esk8_0)))|~m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_50]), c_0_51]), c_0_52])]), c_0_53])).
% 0.17/0.38  cnf(c_0_66, plain, (v2_struct_0(X1)|r3_lattices(X1,X2,k16_lattice3(X1,X3))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r3_lattice3(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.17/0.38  cnf(c_0_67, negated_conjecture, (r3_lattice3(X1,k16_lattice3(X1,a_2_2_lattice3(X2,esk7_0)),a_2_2_lattice3(X2,esk8_0))|v2_struct_0(X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v4_lattice3(X2)|~v10_lattices(X1)|~v10_lattices(X2)|~m1_subset_1(esk2_3(X1,k16_lattice3(X1,a_2_2_lattice3(X2,esk7_0)),a_2_2_lattice3(X2,esk8_0)),u1_struct_0(X1))|~l3_lattices(X1)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_64]), c_0_27])).
% 0.17/0.38  cnf(c_0_68, plain, (r3_lattice3(X1,X2,a_2_2_lattice3(X3,X4))|m1_subset_1(esk2_3(X1,X2,a_2_2_lattice3(X3,X4)),u1_struct_0(X3))|v2_struct_0(X1)|v2_struct_0(X3)|~v4_lattice3(X3)|~v10_lattices(X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X3)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_34, c_0_46])).
% 0.17/0.38  cnf(c_0_69, negated_conjecture, (~r3_lattice3(esk6_0,k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,esk7_0)),a_2_2_lattice3(esk6_0,esk8_0))|~m1_subset_1(k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,esk7_0)),u1_struct_0(esk6_0))|~m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_50]), c_0_51]), c_0_52])]), c_0_53])).
% 0.17/0.38  cnf(c_0_70, negated_conjecture, (r3_lattice3(X1,k16_lattice3(X1,a_2_2_lattice3(X1,esk7_0)),a_2_2_lattice3(X1,esk8_0))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_27])).
% 0.17/0.38  cnf(c_0_71, negated_conjecture, (~m1_subset_1(k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,esk7_0)),u1_struct_0(esk6_0))|~m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_50]), c_0_51]), c_0_52])]), c_0_53])).
% 0.17/0.38  cnf(c_0_72, negated_conjecture, (~m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_27]), c_0_52])]), c_0_53])).
% 0.17/0.38  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_27]), c_0_52])]), c_0_53]), ['proof']).
% 0.17/0.38  # SZS output end CNFRefutation
% 0.17/0.38  # Proof object total steps             : 74
% 0.17/0.38  # Proof object clause steps            : 55
% 0.17/0.38  # Proof object formula steps           : 19
% 0.17/0.38  # Proof object conjectures             : 30
% 0.17/0.38  # Proof object clause conjectures      : 27
% 0.17/0.38  # Proof object formula conjectures     : 3
% 0.17/0.38  # Proof object initial clauses used    : 24
% 0.17/0.38  # Proof object initial formulas used   : 9
% 0.17/0.38  # Proof object generating inferences   : 30
% 0.17/0.38  # Proof object simplifying inferences  : 46
% 0.17/0.38  # Training examples: 0 positive, 0 negative
% 0.17/0.38  # Parsed axioms                        : 10
% 0.17/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.38  # Initial clauses                      : 30
% 0.17/0.38  # Removed in clause preprocessing      : 0
% 0.17/0.38  # Initial clauses in saturation        : 30
% 0.17/0.38  # Processed clauses                    : 225
% 0.17/0.38  # ...of these trivial                  : 0
% 0.17/0.38  # ...subsumed                          : 60
% 0.17/0.38  # ...remaining for further processing  : 165
% 0.17/0.38  # Other redundant clauses eliminated   : 1
% 0.17/0.38  # Clauses deleted for lack of memory   : 0
% 0.17/0.38  # Backward-subsumed                    : 16
% 0.17/0.38  # Backward-rewritten                   : 0
% 0.17/0.38  # Generated clauses                    : 215
% 0.17/0.38  # ...of the previous two non-trivial   : 210
% 0.17/0.38  # Contextual simplify-reflections      : 27
% 0.17/0.38  # Paramodulations                      : 212
% 0.17/0.38  # Factorizations                       : 0
% 0.17/0.38  # Equation resolutions                 : 3
% 0.17/0.38  # Propositional unsat checks           : 0
% 0.17/0.38  #    Propositional check models        : 0
% 0.17/0.38  #    Propositional check unsatisfiable : 0
% 0.17/0.38  #    Propositional clauses             : 0
% 0.17/0.38  #    Propositional clauses after purity: 0
% 0.17/0.38  #    Propositional unsat core size     : 0
% 0.17/0.38  #    Propositional preprocessing time  : 0.000
% 0.17/0.38  #    Propositional encoding time       : 0.000
% 0.17/0.38  #    Propositional solver time         : 0.000
% 0.17/0.38  #    Success case prop preproc time    : 0.000
% 0.17/0.38  #    Success case prop encoding time   : 0.000
% 0.17/0.38  #    Success case prop solver time     : 0.000
% 0.17/0.38  # Current number of processed clauses  : 118
% 0.17/0.38  #    Positive orientable unit clauses  : 5
% 0.17/0.38  #    Positive unorientable unit clauses: 0
% 0.17/0.38  #    Negative unit clauses             : 2
% 0.17/0.38  #    Non-unit-clauses                  : 111
% 0.17/0.38  # Current number of unprocessed clauses: 43
% 0.17/0.38  # ...number of literals in the above   : 448
% 0.17/0.38  # Current number of archived formulas  : 0
% 0.17/0.38  # Current number of archived clauses   : 46
% 0.17/0.38  # Clause-clause subsumption calls (NU) : 9385
% 0.17/0.38  # Rec. Clause-clause subsumption calls : 362
% 0.17/0.38  # Non-unit clause-clause subsumptions  : 103
% 0.17/0.38  # Unit Clause-clause subsumption calls : 43
% 0.17/0.38  # Rewrite failures with RHS unbound    : 0
% 0.17/0.38  # BW rewrite match attempts            : 3
% 0.17/0.38  # BW rewrite match successes           : 0
% 0.17/0.38  # Condensation attempts                : 0
% 0.17/0.38  # Condensation successes               : 0
% 0.17/0.38  # Termbank termtop insertions          : 11423
% 0.17/0.38  
% 0.17/0.38  # -------------------------------------------------
% 0.17/0.38  # User time                : 0.055 s
% 0.17/0.38  # System time              : 0.005 s
% 0.17/0.38  # Total time               : 0.059 s
% 0.17/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
