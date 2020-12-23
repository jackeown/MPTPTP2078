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
% DateTime   : Thu Dec  3 11:15:04 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 180 expanded)
%              Number of clauses        :   47 (  71 expanded)
%              Number of leaves         :   12 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  507 (1392 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   40 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X2,X3)
      <=> r1_lattices(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

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

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(dt_k16_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

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

fof(t37_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] : k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).

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

fof(c_0_12,plain,(
    ! [X12,X13,X14] :
      ( ( ~ r3_lattices(X12,X13,X14)
        | r1_lattices(X12,X13,X14)
        | v2_struct_0(X12)
        | ~ v6_lattices(X12)
        | ~ v8_lattices(X12)
        | ~ v9_lattices(X12)
        | ~ l3_lattices(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12)) )
      & ( ~ r1_lattices(X12,X13,X14)
        | r3_lattices(X12,X13,X14)
        | v2_struct_0(X12)
        | ~ v6_lattices(X12)
        | ~ v8_lattices(X12)
        | ~ v9_lattices(X12)
        | ~ l3_lattices(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

fof(c_0_13,plain,(
    ! [X11] :
      ( ( ~ v2_struct_0(X11)
        | v2_struct_0(X11)
        | ~ v10_lattices(X11)
        | ~ l3_lattices(X11) )
      & ( v4_lattices(X11)
        | v2_struct_0(X11)
        | ~ v10_lattices(X11)
        | ~ l3_lattices(X11) )
      & ( v5_lattices(X11)
        | v2_struct_0(X11)
        | ~ v10_lattices(X11)
        | ~ l3_lattices(X11) )
      & ( v6_lattices(X11)
        | v2_struct_0(X11)
        | ~ v10_lattices(X11)
        | ~ l3_lattices(X11) )
      & ( v7_lattices(X11)
        | v2_struct_0(X11)
        | ~ v10_lattices(X11)
        | ~ l3_lattices(X11) )
      & ( v8_lattices(X11)
        | v2_struct_0(X11)
        | ~ v10_lattices(X11)
        | ~ l3_lattices(X11) )
      & ( v9_lattices(X11)
        | v2_struct_0(X11)
        | ~ v10_lattices(X11)
        | ~ l3_lattices(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_14,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( ~ r4_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ r2_hidden(X24,X23)
        | r1_lattices(X21,X24,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( m1_subset_1(esk3_3(X21,X22,X25),u1_struct_0(X21))
        | r4_lattice3(X21,X22,X25)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( r2_hidden(esk3_3(X21,X22,X25),X25)
        | r4_lattice3(X21,X22,X25)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( ~ r1_lattices(X21,esk3_3(X21,X22,X25),X22)
        | r4_lattice3(X21,X22,X25)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

cnf(c_0_15,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,(
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

cnf(c_0_20,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk3_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X45,X46,X47] :
      ( ( r3_lattices(X45,X46,k15_lattice3(X45,X47))
        | ~ r2_hidden(X46,X47)
        | ~ m1_subset_1(X46,u1_struct_0(X45))
        | v2_struct_0(X45)
        | ~ v10_lattices(X45)
        | ~ v4_lattice3(X45)
        | ~ l3_lattices(X45) )
      & ( r3_lattices(X45,k16_lattice3(X45,X47),X46)
        | ~ r2_hidden(X46,X47)
        | ~ m1_subset_1(X46,u1_struct_0(X45))
        | v2_struct_0(X45)
        | ~ v10_lattices(X45)
        | ~ v4_lattice3(X45)
        | ~ l3_lattices(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

fof(c_0_24,plain,(
    ! [X27,X28] :
      ( v2_struct_0(X27)
      | ~ l3_lattices(X27)
      | m1_subset_1(k15_lattice3(X27,X28),u1_struct_0(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_25,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v10_lattices(esk6_0)
    & v4_lattice3(esk6_0)
    & l3_lattices(esk6_0)
    & r1_tarski(esk7_0,esk8_0)
    & ( ~ r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0))
      | ~ r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

cnf(c_0_27,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,esk3_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( ~ r3_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r2_hidden(X18,X17)
        | r1_lattices(X15,X16,X18)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( m1_subset_1(esk2_3(X15,X16,X19),u1_struct_0(X15))
        | r3_lattice3(X15,X16,X19)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( r2_hidden(esk2_3(X15,X16,X19),X19)
        | r3_lattice3(X15,X16,X19)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( ~ r1_lattices(X15,X16,esk2_3(X15,X16,X19))
        | r3_lattice3(X15,X16,X19)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

cnf(c_0_33,plain,
    ( r4_lattice3(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk3_3(X1,k15_lattice3(X1,X2),X3),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk3_3(X1,k15_lattice3(X1,X2),X3),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk2_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_37,plain,(
    ! [X29,X30] :
      ( v2_struct_0(X29)
      | ~ l3_lattices(X29)
      | m1_subset_1(k16_lattice3(X29,X30),u1_struct_0(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

fof(c_0_38,plain,(
    ! [X31,X32,X33,X35,X36] :
      ( ( m1_subset_1(esk4_3(X31,X32,X33),u1_struct_0(X32))
        | ~ r2_hidden(X31,a_2_2_lattice3(X32,X33))
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ v4_lattice3(X32)
        | ~ l3_lattices(X32) )
      & ( X31 = esk4_3(X31,X32,X33)
        | ~ r2_hidden(X31,a_2_2_lattice3(X32,X33))
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ v4_lattice3(X32)
        | ~ l3_lattices(X32) )
      & ( r4_lattice3(X32,esk4_3(X31,X32,X33),X33)
        | ~ r2_hidden(X31,a_2_2_lattice3(X32,X33))
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ v4_lattice3(X32)
        | ~ l3_lattices(X32) )
      & ( ~ m1_subset_1(X36,u1_struct_0(X32))
        | X31 != X36
        | ~ r4_lattice3(X32,X36,X35)
        | r2_hidden(X31,a_2_2_lattice3(X32,X35))
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ v4_lattice3(X32)
        | ~ l3_lattices(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).

cnf(c_0_39,negated_conjecture,
    ( r4_lattice3(X1,k15_lattice3(X1,esk8_0),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk3_3(X1,k15_lattice3(X1,esk8_0),X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk3_3(X1,k15_lattice3(X1,esk8_0),X2),esk7_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,esk2_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_21]),c_0_36])).

cnf(c_0_42,plain,
    ( r3_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_44,plain,(
    ! [X43,X44] :
      ( v2_struct_0(X43)
      | ~ v10_lattices(X43)
      | ~ v4_lattice3(X43)
      | ~ l3_lattices(X43)
      | k15_lattice3(X43,X44) = k16_lattice3(X43,a_2_2_lattice3(X43,X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( X1 = esk4_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( r2_hidden(X3,a_2_2_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r4_lattice3(X2,X1,X4)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( r4_lattice3(X1,k15_lattice3(X1,esk8_0),esk7_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk3_3(X1,k15_lattice3(X1,esk8_0),esk7_0),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_29])).

cnf(c_0_49,plain,
    ( r3_lattice3(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk2_3(X1,k16_lattice3(X1,X2),X3),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk2_3(X1,k16_lattice3(X1,X2),X3),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_2_lattice3(X1,X3))
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r4_lattice3(X1,k15_lattice3(X1,esk8_0),esk7_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_22]),c_0_29])).

cnf(c_0_54,negated_conjecture,
    ( r3_lattice3(X1,k16_lattice3(X1,esk8_0),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk2_3(X1,k16_lattice3(X1,esk8_0),X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk2_3(X1,k16_lattice3(X1,esk8_0),X2),esk7_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_34])).

cnf(c_0_55,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_56,plain,
    ( r3_lattices(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X3,a_2_2_lattice3(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_50]),c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(k15_lattice3(X1,esk8_0),a_2_2_lattice3(X1,esk7_0))
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_29])).

fof(c_0_58,plain,(
    ! [X37,X38,X39,X40,X41] :
      ( ( r3_lattice3(X37,X38,X39)
        | X38 != k16_lattice3(X37,X39)
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v10_lattices(X37)
        | ~ v4_lattice3(X37)
        | ~ l3_lattices(X37) )
      & ( ~ m1_subset_1(X40,u1_struct_0(X37))
        | ~ r3_lattice3(X37,X40,X39)
        | r3_lattices(X37,X40,X38)
        | X38 != k16_lattice3(X37,X39)
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v10_lattices(X37)
        | ~ v4_lattice3(X37)
        | ~ l3_lattices(X37) )
      & ( m1_subset_1(esk5_3(X37,X38,X41),u1_struct_0(X37))
        | ~ r3_lattice3(X37,X38,X41)
        | X38 = k16_lattice3(X37,X41)
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v10_lattices(X37)
        | ~ v4_lattice3(X37)
        | ~ l3_lattices(X37) )
      & ( r3_lattice3(X37,esk5_3(X37,X38,X41),X41)
        | ~ r3_lattice3(X37,X38,X41)
        | X38 = k16_lattice3(X37,X41)
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v10_lattices(X37)
        | ~ v4_lattice3(X37)
        | ~ l3_lattices(X37) )
      & ( ~ r3_lattices(X37,esk5_3(X37,X38,X41),X38)
        | ~ r3_lattice3(X37,X38,X41)
        | X38 = k16_lattice3(X37,X41)
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v10_lattices(X37)
        | ~ v4_lattice3(X37)
        | ~ l3_lattices(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

cnf(c_0_59,negated_conjecture,
    ( r3_lattice3(X1,k16_lattice3(X1,esk8_0),esk7_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk2_3(X1,k16_lattice3(X1,esk8_0),esk7_0),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_43])).

cnf(c_0_60,negated_conjecture,
    ( ~ r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0))
    | ~ r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_61,negated_conjecture,
    ( r3_lattices(X1,k15_lattice3(X1,esk7_0),k15_lattice3(X1,esk8_0))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( v4_lattice3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_63,negated_conjecture,
    ( v10_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_64,negated_conjecture,
    ( l3_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_65,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_66,plain,
    ( r3_lattices(X2,X1,X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_lattice3(X2,X1,X3)
    | X4 != k16_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( r3_lattice3(X1,k16_lattice3(X1,esk8_0),esk7_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_36]),c_0_43])).

cnf(c_0_68,negated_conjecture,
    ( ~ r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63]),c_0_64])]),c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( r3_lattices(X1,k16_lattice3(X1,esk8_0),X2)
    | v2_struct_0(X1)
    | X2 != k16_lattice3(X1,esk7_0)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_43])).

cnf(c_0_70,negated_conjecture,
    ( ~ m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_62]),c_0_63]),c_0_64])]),c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_43]),c_0_64])]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.20/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.029 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.20/0.39  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.20/0.39  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 0.20/0.39  fof(t46_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_lattice3)).
% 0.20/0.39  fof(t38_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 0.20/0.39  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.20/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.39  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 0.20/0.39  fof(dt_k16_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 0.20/0.39  fof(fraenkel_a_2_2_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_2_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r4_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 0.20/0.39  fof(t37_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_lattice3)).
% 0.20/0.39  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 0.20/0.39  fof(c_0_12, plain, ![X12, X13, X14]:((~r3_lattices(X12,X13,X14)|r1_lattices(X12,X13,X14)|(v2_struct_0(X12)|~v6_lattices(X12)|~v8_lattices(X12)|~v9_lattices(X12)|~l3_lattices(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))))&(~r1_lattices(X12,X13,X14)|r3_lattices(X12,X13,X14)|(v2_struct_0(X12)|~v6_lattices(X12)|~v8_lattices(X12)|~v9_lattices(X12)|~l3_lattices(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.20/0.39  fof(c_0_13, plain, ![X11]:(((((((~v2_struct_0(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11))&(v4_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11)))&(v5_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11)))&(v6_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11)))&(v7_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11)))&(v8_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11)))&(v9_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.20/0.39  fof(c_0_14, plain, ![X21, X22, X23, X24, X25]:((~r4_lattice3(X21,X22,X23)|(~m1_subset_1(X24,u1_struct_0(X21))|(~r2_hidden(X24,X23)|r1_lattices(X21,X24,X22)))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&((m1_subset_1(esk3_3(X21,X22,X25),u1_struct_0(X21))|r4_lattice3(X21,X22,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&((r2_hidden(esk3_3(X21,X22,X25),X25)|r4_lattice3(X21,X22,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&(~r1_lattices(X21,esk3_3(X21,X22,X25),X22)|r4_lattice3(X21,X22,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.20/0.39  cnf(c_0_15, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_16, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_17, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_18, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  fof(c_0_19, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2)))))), inference(assume_negation,[status(cth)],[t46_lattice3])).
% 0.20/0.39  cnf(c_0_20, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk3_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_21, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])).
% 0.20/0.39  cnf(c_0_22, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  fof(c_0_23, plain, ![X45, X46, X47]:((r3_lattices(X45,X46,k15_lattice3(X45,X47))|~r2_hidden(X46,X47)|~m1_subset_1(X46,u1_struct_0(X45))|(v2_struct_0(X45)|~v10_lattices(X45)|~v4_lattice3(X45)|~l3_lattices(X45)))&(r3_lattices(X45,k16_lattice3(X45,X47),X46)|~r2_hidden(X46,X47)|~m1_subset_1(X46,u1_struct_0(X45))|(v2_struct_0(X45)|~v10_lattices(X45)|~v4_lattice3(X45)|~l3_lattices(X45)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).
% 0.20/0.39  fof(c_0_24, plain, ![X27, X28]:(v2_struct_0(X27)|~l3_lattices(X27)|m1_subset_1(k15_lattice3(X27,X28),u1_struct_0(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.20/0.39  fof(c_0_25, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.39  fof(c_0_26, negated_conjecture, ((((~v2_struct_0(esk6_0)&v10_lattices(esk6_0))&v4_lattice3(esk6_0))&l3_lattices(esk6_0))&(r1_tarski(esk7_0,esk8_0)&(~r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0))|~r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.20/0.39  cnf(c_0_27, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,esk3_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.20/0.39  cnf(c_0_28, plain, (r3_lattices(X1,X2,k15_lattice3(X1,X3))|v2_struct_0(X1)|~r2_hidden(X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_29, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (r1_tarski(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  fof(c_0_32, plain, ![X15, X16, X17, X18, X19]:((~r3_lattice3(X15,X16,X17)|(~m1_subset_1(X18,u1_struct_0(X15))|(~r2_hidden(X18,X17)|r1_lattices(X15,X16,X18)))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&((m1_subset_1(esk2_3(X15,X16,X19),u1_struct_0(X15))|r3_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&((r2_hidden(esk2_3(X15,X16,X19),X19)|r3_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&(~r1_lattices(X15,X16,esk2_3(X15,X16,X19))|r3_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.20/0.39  cnf(c_0_33, plain, (r4_lattice3(X1,k15_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk3_3(X1,k15_lattice3(X1,X2),X3),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(esk3_3(X1,k15_lattice3(X1,X2),X3),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.39  cnf(c_0_35, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk2_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.39  cnf(c_0_36, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.39  fof(c_0_37, plain, ![X29, X30]:(v2_struct_0(X29)|~l3_lattices(X29)|m1_subset_1(k16_lattice3(X29,X30),u1_struct_0(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).
% 0.20/0.39  fof(c_0_38, plain, ![X31, X32, X33, X35, X36]:((((m1_subset_1(esk4_3(X31,X32,X33),u1_struct_0(X32))|~r2_hidden(X31,a_2_2_lattice3(X32,X33))|(v2_struct_0(X32)|~v10_lattices(X32)|~v4_lattice3(X32)|~l3_lattices(X32)))&(X31=esk4_3(X31,X32,X33)|~r2_hidden(X31,a_2_2_lattice3(X32,X33))|(v2_struct_0(X32)|~v10_lattices(X32)|~v4_lattice3(X32)|~l3_lattices(X32))))&(r4_lattice3(X32,esk4_3(X31,X32,X33),X33)|~r2_hidden(X31,a_2_2_lattice3(X32,X33))|(v2_struct_0(X32)|~v10_lattices(X32)|~v4_lattice3(X32)|~l3_lattices(X32))))&(~m1_subset_1(X36,u1_struct_0(X32))|X31!=X36|~r4_lattice3(X32,X36,X35)|r2_hidden(X31,a_2_2_lattice3(X32,X35))|(v2_struct_0(X32)|~v10_lattices(X32)|~v4_lattice3(X32)|~l3_lattices(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).
% 0.20/0.39  cnf(c_0_39, negated_conjecture, (r4_lattice3(X1,k15_lattice3(X1,esk8_0),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk3_3(X1,k15_lattice3(X1,esk8_0),X2),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(esk3_3(X1,k15_lattice3(X1,esk8_0),X2),esk7_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.39  cnf(c_0_40, plain, (r2_hidden(esk3_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_41, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,esk2_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_21]), c_0_36])).
% 0.20/0.39  cnf(c_0_42, plain, (r3_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_43, plain, (v2_struct_0(X1)|m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.39  fof(c_0_44, plain, ![X43, X44]:(v2_struct_0(X43)|~v10_lattices(X43)|~v4_lattice3(X43)|~l3_lattices(X43)|k15_lattice3(X43,X44)=k16_lattice3(X43,a_2_2_lattice3(X43,X44))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).
% 0.20/0.39  cnf(c_0_45, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.39  cnf(c_0_46, plain, (X1=esk4_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.39  cnf(c_0_47, plain, (r2_hidden(X3,a_2_2_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r4_lattice3(X2,X1,X4)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (r4_lattice3(X1,k15_lattice3(X1,esk8_0),esk7_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk3_3(X1,k15_lattice3(X1,esk8_0),esk7_0),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_29])).
% 0.20/0.39  cnf(c_0_49, plain, (r3_lattice3(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk2_3(X1,k16_lattice3(X1,X2),X3),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(esk2_3(X1,k16_lattice3(X1,X2),X3),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.20/0.39  cnf(c_0_50, plain, (v2_struct_0(X1)|k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.39  cnf(c_0_51, plain, (m1_subset_1(X1,u1_struct_0(X2))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)|~r2_hidden(X1,a_2_2_lattice3(X2,X3))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.39  cnf(c_0_52, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_2_lattice3(X1,X3))|~v4_lattice3(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_47])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (r4_lattice3(X1,k15_lattice3(X1,esk8_0),esk7_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_22]), c_0_29])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (r3_lattice3(X1,k16_lattice3(X1,esk8_0),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk2_3(X1,k16_lattice3(X1,esk8_0),X2),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(esk2_3(X1,k16_lattice3(X1,esk8_0),X2),esk7_0)), inference(spm,[status(thm)],[c_0_49, c_0_34])).
% 0.20/0.39  cnf(c_0_55, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.39  cnf(c_0_56, plain, (r3_lattices(X1,k15_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X3,a_2_2_lattice3(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_50]), c_0_51])).
% 0.20/0.39  cnf(c_0_57, negated_conjecture, (v2_struct_0(X1)|r2_hidden(k15_lattice3(X1,esk8_0),a_2_2_lattice3(X1,esk7_0))|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_29])).
% 0.20/0.39  fof(c_0_58, plain, ![X37, X38, X39, X40, X41]:(((r3_lattice3(X37,X38,X39)|X38!=k16_lattice3(X37,X39)|~m1_subset_1(X38,u1_struct_0(X37))|(v2_struct_0(X37)|~v10_lattices(X37)|~v4_lattice3(X37)|~l3_lattices(X37)))&(~m1_subset_1(X40,u1_struct_0(X37))|(~r3_lattice3(X37,X40,X39)|r3_lattices(X37,X40,X38))|X38!=k16_lattice3(X37,X39)|~m1_subset_1(X38,u1_struct_0(X37))|(v2_struct_0(X37)|~v10_lattices(X37)|~v4_lattice3(X37)|~l3_lattices(X37))))&((m1_subset_1(esk5_3(X37,X38,X41),u1_struct_0(X37))|~r3_lattice3(X37,X38,X41)|X38=k16_lattice3(X37,X41)|~m1_subset_1(X38,u1_struct_0(X37))|(v2_struct_0(X37)|~v10_lattices(X37)|~v4_lattice3(X37)|~l3_lattices(X37)))&((r3_lattice3(X37,esk5_3(X37,X38,X41),X41)|~r3_lattice3(X37,X38,X41)|X38=k16_lattice3(X37,X41)|~m1_subset_1(X38,u1_struct_0(X37))|(v2_struct_0(X37)|~v10_lattices(X37)|~v4_lattice3(X37)|~l3_lattices(X37)))&(~r3_lattices(X37,esk5_3(X37,X38,X41),X38)|~r3_lattice3(X37,X38,X41)|X38=k16_lattice3(X37,X41)|~m1_subset_1(X38,u1_struct_0(X37))|(v2_struct_0(X37)|~v10_lattices(X37)|~v4_lattice3(X37)|~l3_lattices(X37)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (r3_lattice3(X1,k16_lattice3(X1,esk8_0),esk7_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk2_3(X1,k16_lattice3(X1,esk8_0),esk7_0),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_43])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (~r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0))|~r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (r3_lattices(X1,k15_lattice3(X1,esk7_0),k15_lattice3(X1,esk8_0))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (v4_lattice3(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (v10_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (l3_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_66, plain, (r3_lattices(X2,X1,X4)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_lattice3(X2,X1,X3)|X4!=k16_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (r3_lattice3(X1,k16_lattice3(X1,esk8_0),esk7_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_36]), c_0_43])).
% 0.20/0.40  cnf(c_0_68, negated_conjecture, (~r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_63]), c_0_64])]), c_0_65])).
% 0.20/0.40  cnf(c_0_69, negated_conjecture, (r3_lattices(X1,k16_lattice3(X1,esk8_0),X2)|v2_struct_0(X1)|X2!=k16_lattice3(X1,esk7_0)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_43])).
% 0.20/0.40  cnf(c_0_70, negated_conjecture, (~m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_62]), c_0_63]), c_0_64])]), c_0_65])).
% 0.20/0.40  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_43]), c_0_64])]), c_0_65]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 72
% 0.20/0.40  # Proof object clause steps            : 47
% 0.20/0.40  # Proof object formula steps           : 25
% 0.20/0.40  # Proof object conjectures             : 22
% 0.20/0.40  # Proof object clause conjectures      : 19
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 26
% 0.20/0.40  # Proof object initial formulas used   : 12
% 0.20/0.40  # Proof object generating inferences   : 20
% 0.20/0.40  # Proof object simplifying inferences  : 27
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 12
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 40
% 0.20/0.40  # Removed in clause preprocessing      : 1
% 0.20/0.40  # Initial clauses in saturation        : 39
% 0.20/0.40  # Processed clauses                    : 195
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 32
% 0.20/0.40  # ...remaining for further processing  : 163
% 0.20/0.40  # Other redundant clauses eliminated   : 1
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 9
% 0.20/0.40  # Backward-rewritten                   : 0
% 0.20/0.40  # Generated clauses                    : 166
% 0.20/0.40  # ...of the previous two non-trivial   : 160
% 0.20/0.40  # Contextual simplify-reflections      : 40
% 0.20/0.40  # Paramodulations                      : 161
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 5
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 114
% 0.20/0.40  #    Positive orientable unit clauses  : 5
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 4
% 0.20/0.40  #    Non-unit-clauses                  : 105
% 0.20/0.40  # Current number of unprocessed clauses: 41
% 0.20/0.40  # ...number of literals in the above   : 389
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 48
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 7660
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 205
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 76
% 0.20/0.40  # Unit Clause-clause subsumption calls : 22
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 3
% 0.20/0.40  # BW rewrite match successes           : 0
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 10343
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.049 s
% 0.20/0.40  # System time              : 0.004 s
% 0.20/0.40  # Total time               : 0.053 s
% 0.20/0.40  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
