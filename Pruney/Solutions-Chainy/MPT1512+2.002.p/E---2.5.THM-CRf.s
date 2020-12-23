%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:04 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 197 expanded)
%              Number of clauses        :   47 (  75 expanded)
%              Number of leaves         :   11 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  495 (1414 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   50 (   5 average)
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

fof(dt_k16_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

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

fof(c_0_11,plain,(
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

fof(c_0_12,plain,(
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
    ! [X34,X35] :
      ( v2_struct_0(X34)
      | ~ l3_lattices(X34)
      | m1_subset_1(k16_lattice3(X34,X35),u1_struct_0(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X27,X28,X29,X30] :
      ( ( r4_lattice3(X27,X29,X28)
        | X29 != k15_lattice3(X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ v4_lattice3(X27)
        | ~ l3_lattices(X27)
        | v2_struct_0(X27)
        | ~ l3_lattices(X27) )
      & ( ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ r4_lattice3(X27,X30,X28)
        | r1_lattices(X27,X29,X30)
        | X29 != k15_lattice3(X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ v4_lattice3(X27)
        | ~ l3_lattices(X27)
        | v2_struct_0(X27)
        | ~ l3_lattices(X27) )
      & ( m1_subset_1(esk4_3(X27,X28,X29),u1_struct_0(X27))
        | ~ r4_lattice3(X27,X29,X28)
        | X29 = k15_lattice3(X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ v4_lattice3(X27)
        | ~ l3_lattices(X27)
        | v2_struct_0(X27)
        | ~ l3_lattices(X27) )
      & ( r4_lattice3(X27,esk4_3(X27,X28,X29),X28)
        | ~ r4_lattice3(X27,X29,X28)
        | X29 = k15_lattice3(X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ v4_lattice3(X27)
        | ~ l3_lattices(X27)
        | v2_struct_0(X27)
        | ~ l3_lattices(X27) )
      & ( ~ r1_lattices(X27,X29,esk4_3(X27,X28,X29))
        | ~ r4_lattice3(X27,X29,X28)
        | X29 = k15_lattice3(X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ v4_lattice3(X27)
        | ~ l3_lattices(X27)
        | v2_struct_0(X27)
        | ~ l3_lattices(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

fof(c_0_17,plain,(
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

cnf(c_0_18,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r3_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_24,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v10_lattices(esk5_0)
    & v4_lattice3(esk5_0)
    & l3_lattices(esk5_0)
    & r1_tarski(esk6_0,esk7_0)
    & ( ~ r3_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0))
      | ~ r3_lattices(esk5_0,k16_lattice3(esk5_0,esk7_0),k16_lattice3(esk5_0,esk6_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

cnf(c_0_26,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_27,plain,(
    ! [X32,X33] :
      ( v2_struct_0(X32)
      | ~ l3_lattices(X32)
      | m1_subset_1(k15_lattice3(X32,X33),u1_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

cnf(c_0_28,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk2_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( r1_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
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

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | r4_lattice3(X1,X2,X3)
    | X2 != k15_lattice3(X1,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r3_lattice3(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk2_3(X1,k16_lattice3(X1,X2),X3),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk2_3(X1,k16_lattice3(X1,X2),X3),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( r4_lattice3(X1,k15_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r3_lattice3(X1,k16_lattice3(X1,esk7_0),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk2_3(X1,k16_lattice3(X1,esk7_0),X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk2_3(X1,k16_lattice3(X1,esk7_0),X2),esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_41,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk3_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( r1_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_34])).

fof(c_0_43,plain,(
    ! [X39,X40,X41] :
      ( v2_struct_0(X39)
      | ~ v10_lattices(X39)
      | ~ v4_lattice3(X39)
      | ~ l3_lattices(X39)
      | ~ m1_subset_1(X40,u1_struct_0(X39))
      | ~ r3_lattice3(X39,X40,X41)
      | r3_lattices(X39,X40,k16_lattice3(X39,X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_lattice3])])])])).

cnf(c_0_44,negated_conjecture,
    ( r3_lattice3(X1,k16_lattice3(X1,esk7_0),esk6_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk2_3(X1,k16_lattice3(X1,esk7_0),esk6_0),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_23])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,plain,
    ( r4_lattice3(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk3_3(X1,k15_lattice3(X1,X2),X3),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk3_3(X1,k15_lattice3(X1,X2),X3),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_34])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,X2,k16_lattice3(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r3_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r3_lattice3(X1,k16_lattice3(X1,esk7_0),esk6_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( r4_lattice3(X1,k15_lattice3(X1,esk7_0),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk3_3(X1,k15_lattice3(X1,esk7_0),X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk3_3(X1,k15_lattice3(X1,esk7_0),X2),esk6_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_36])).

cnf(c_0_50,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( ~ r3_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0))
    | ~ r3_lattices(esk5_0,k16_lattice3(esk5_0,esk7_0),k16_lattice3(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_52,negated_conjecture,
    ( r3_lattices(X1,k16_lattice3(X1,esk7_0),k16_lattice3(X1,esk6_0))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( v4_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_54,negated_conjecture,
    ( v10_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_55,negated_conjecture,
    ( l3_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_56,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_57,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_58,plain,
    ( r1_lattices(X2,X4,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r4_lattice3(X2,X1,X3)
    | X4 != k15_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_59,negated_conjecture,
    ( r4_lattice3(X1,k15_lattice3(X1,esk7_0),esk6_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk3_3(X1,k15_lattice3(X1,esk7_0),esk6_0),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_34])).

cnf(c_0_60,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_61,negated_conjecture,
    ( ~ r3_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54]),c_0_55])]),c_0_56])).

cnf(c_0_62,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_22]),c_0_20]),c_0_21])).

cnf(c_0_63,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( r4_lattice3(X1,k15_lattice3(X1,esk7_0),esk6_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_34])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0))
    | ~ m1_subset_1(k15_lattice3(esk5_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(k15_lattice3(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_54]),c_0_55])]),c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( r1_lattices(X1,X2,k15_lattice3(X1,esk7_0))
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,esk6_0)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_34])).

cnf(c_0_67,negated_conjecture,
    ( ~ m1_subset_1(k15_lattice3(esk5_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(k15_lattice3(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_53]),c_0_54]),c_0_55])]),c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( ~ m1_subset_1(k15_lattice3(esk5_0,esk6_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_34]),c_0_55])]),c_0_56])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_34]),c_0_55])]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.13/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.029 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.13/0.39  fof(t38_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 0.13/0.39  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.13/0.39  fof(dt_k16_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 0.13/0.39  fof(t46_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_lattice3)).
% 0.13/0.39  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 0.13/0.39  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 0.13/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.39  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.13/0.39  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 0.13/0.39  fof(t40_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)=>r3_lattices(X1,X2,k16_lattice3(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_lattice3)).
% 0.13/0.39  fof(c_0_11, plain, ![X12, X13, X14]:((~r3_lattices(X12,X13,X14)|r1_lattices(X12,X13,X14)|(v2_struct_0(X12)|~v6_lattices(X12)|~v8_lattices(X12)|~v9_lattices(X12)|~l3_lattices(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))))&(~r1_lattices(X12,X13,X14)|r3_lattices(X12,X13,X14)|(v2_struct_0(X12)|~v6_lattices(X12)|~v8_lattices(X12)|~v9_lattices(X12)|~l3_lattices(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.13/0.39  fof(c_0_12, plain, ![X36, X37, X38]:((r3_lattices(X36,X37,k15_lattice3(X36,X38))|~r2_hidden(X37,X38)|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~v10_lattices(X36)|~v4_lattice3(X36)|~l3_lattices(X36)))&(r3_lattices(X36,k16_lattice3(X36,X38),X37)|~r2_hidden(X37,X38)|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~v10_lattices(X36)|~v4_lattice3(X36)|~l3_lattices(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).
% 0.13/0.39  fof(c_0_13, plain, ![X11]:(((((((~v2_struct_0(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11))&(v4_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11)))&(v5_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11)))&(v6_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11)))&(v7_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11)))&(v8_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11)))&(v9_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.13/0.39  fof(c_0_14, plain, ![X34, X35]:(v2_struct_0(X34)|~l3_lattices(X34)|m1_subset_1(k16_lattice3(X34,X35),u1_struct_0(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).
% 0.13/0.39  fof(c_0_15, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2)))))), inference(assume_negation,[status(cth)],[t46_lattice3])).
% 0.13/0.39  fof(c_0_16, plain, ![X27, X28, X29, X30]:(((r4_lattice3(X27,X29,X28)|X29!=k15_lattice3(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27))|(v2_struct_0(X27)|~l3_lattices(X27)))&(~m1_subset_1(X30,u1_struct_0(X27))|(~r4_lattice3(X27,X30,X28)|r1_lattices(X27,X29,X30))|X29!=k15_lattice3(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27))|(v2_struct_0(X27)|~l3_lattices(X27))))&((m1_subset_1(esk4_3(X27,X28,X29),u1_struct_0(X27))|~r4_lattice3(X27,X29,X28)|X29=k15_lattice3(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27))|(v2_struct_0(X27)|~l3_lattices(X27)))&((r4_lattice3(X27,esk4_3(X27,X28,X29),X28)|~r4_lattice3(X27,X29,X28)|X29=k15_lattice3(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27))|(v2_struct_0(X27)|~l3_lattices(X27)))&(~r1_lattices(X27,X29,esk4_3(X27,X28,X29))|~r4_lattice3(X27,X29,X28)|X29=k15_lattice3(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27))|(v2_struct_0(X27)|~l3_lattices(X27)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.13/0.39  fof(c_0_17, plain, ![X15, X16, X17, X18, X19]:((~r3_lattice3(X15,X16,X17)|(~m1_subset_1(X18,u1_struct_0(X15))|(~r2_hidden(X18,X17)|r1_lattices(X15,X16,X18)))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&((m1_subset_1(esk2_3(X15,X16,X19),u1_struct_0(X15))|r3_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&((r2_hidden(esk2_3(X15,X16,X19),X19)|r3_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&(~r1_lattices(X15,X16,esk2_3(X15,X16,X19))|r3_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.13/0.39  cnf(c_0_18, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_19, plain, (r3_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_20, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_21, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_22, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_23, plain, (v2_struct_0(X1)|m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  fof(c_0_24, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.39  fof(c_0_25, negated_conjecture, ((((~v2_struct_0(esk5_0)&v10_lattices(esk5_0))&v4_lattice3(esk5_0))&l3_lattices(esk5_0))&(r1_tarski(esk6_0,esk7_0)&(~r3_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0))|~r3_lattices(esk5_0,k16_lattice3(esk5_0,esk7_0),k16_lattice3(esk5_0,esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.13/0.39  cnf(c_0_26, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X1)|X2!=k15_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  fof(c_0_27, plain, ![X32, X33]:(v2_struct_0(X32)|~l3_lattices(X32)|m1_subset_1(k15_lattice3(X32,X33),u1_struct_0(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.13/0.39  cnf(c_0_28, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk2_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_29, plain, (r1_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.13/0.39  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_31, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  fof(c_0_32, plain, ![X21, X22, X23, X24, X25]:((~r4_lattice3(X21,X22,X23)|(~m1_subset_1(X24,u1_struct_0(X21))|(~r2_hidden(X24,X23)|r1_lattices(X21,X24,X22)))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&((m1_subset_1(esk3_3(X21,X22,X25),u1_struct_0(X21))|r4_lattice3(X21,X22,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&((r2_hidden(esk3_3(X21,X22,X25),X25)|r4_lattice3(X21,X22,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&(~r1_lattices(X21,esk3_3(X21,X22,X25),X22)|r4_lattice3(X21,X22,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.13/0.39  cnf(c_0_33, plain, (v2_struct_0(X1)|r4_lattice3(X1,X2,X3)|X2!=k15_lattice3(X1,X3)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_34, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_35, plain, (r3_lattice3(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk2_3(X1,k16_lattice3(X1,X2),X3),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(esk2_3(X1,k16_lattice3(X1,X2),X3),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_23])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.39  cnf(c_0_37, plain, (r1_lattices(X1,X4,X2)|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.39  cnf(c_0_38, plain, (r4_lattice3(X1,k15_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_33]), c_0_34])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (r3_lattice3(X1,k16_lattice3(X1,esk7_0),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk2_3(X1,k16_lattice3(X1,esk7_0),X2),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(esk2_3(X1,k16_lattice3(X1,esk7_0),X2),esk6_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.39  cnf(c_0_40, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_41, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk3_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.39  cnf(c_0_42, plain, (r1_lattices(X1,X2,k15_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_34])).
% 0.13/0.39  fof(c_0_43, plain, ![X39, X40, X41]:(v2_struct_0(X39)|~v10_lattices(X39)|~v4_lattice3(X39)|~l3_lattices(X39)|(~m1_subset_1(X40,u1_struct_0(X39))|(~r3_lattice3(X39,X40,X41)|r3_lattices(X39,X40,k16_lattice3(X39,X41))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_lattice3])])])])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (r3_lattice3(X1,k16_lattice3(X1,esk7_0),esk6_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk2_3(X1,k16_lattice3(X1,esk7_0),esk6_0),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_23])).
% 0.13/0.39  cnf(c_0_45, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_46, plain, (r4_lattice3(X1,k15_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk3_3(X1,k15_lattice3(X1,X2),X3),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(esk3_3(X1,k15_lattice3(X1,X2),X3),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_34])).
% 0.13/0.39  cnf(c_0_47, plain, (v2_struct_0(X1)|r3_lattices(X1,X2,k16_lattice3(X1,X3))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r3_lattice3(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (r3_lattice3(X1,k16_lattice3(X1,esk7_0),esk6_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_23])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (r4_lattice3(X1,k15_lattice3(X1,esk7_0),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk3_3(X1,k15_lattice3(X1,esk7_0),X2),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(esk3_3(X1,k15_lattice3(X1,esk7_0),X2),esk6_0)), inference(spm,[status(thm)],[c_0_46, c_0_36])).
% 0.13/0.39  cnf(c_0_50, plain, (r2_hidden(esk3_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (~r3_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0))|~r3_lattices(esk5_0,k16_lattice3(esk5_0,esk7_0),k16_lattice3(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (r3_lattices(X1,k16_lattice3(X1,esk7_0),k16_lattice3(X1,esk6_0))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_23])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (v4_lattice3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_54, negated_conjecture, (v10_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (l3_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_57, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_58, plain, (r1_lattices(X2,X4,X1)|v2_struct_0(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r4_lattice3(X2,X1,X3)|X4!=k15_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (r4_lattice3(X1,k15_lattice3(X1,esk7_0),esk6_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk3_3(X1,k15_lattice3(X1,esk7_0),esk6_0),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_34])).
% 0.13/0.39  cnf(c_0_60, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (~r3_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54]), c_0_55])]), c_0_56])).
% 0.13/0.39  cnf(c_0_62, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_22]), c_0_20]), c_0_21])).
% 0.13/0.39  cnf(c_0_63, plain, (v2_struct_0(X2)|r1_lattices(X2,X4,X1)|X4!=k15_lattice3(X2,X3)|~l3_lattices(X2)|~v10_lattices(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))), inference(cn,[status(thm)],[c_0_58])).
% 0.13/0.39  cnf(c_0_64, negated_conjecture, (r4_lattice3(X1,k15_lattice3(X1,esk7_0),esk6_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_34])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, (~r1_lattices(esk5_0,k15_lattice3(esk5_0,esk6_0),k15_lattice3(esk5_0,esk7_0))|~m1_subset_1(k15_lattice3(esk5_0,esk7_0),u1_struct_0(esk5_0))|~m1_subset_1(k15_lattice3(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_54]), c_0_55])]), c_0_56])).
% 0.13/0.39  cnf(c_0_66, negated_conjecture, (r1_lattices(X1,X2,k15_lattice3(X1,esk7_0))|v2_struct_0(X1)|X2!=k15_lattice3(X1,esk6_0)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_34])).
% 0.13/0.39  cnf(c_0_67, negated_conjecture, (~m1_subset_1(k15_lattice3(esk5_0,esk7_0),u1_struct_0(esk5_0))|~m1_subset_1(k15_lattice3(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_53]), c_0_54]), c_0_55])]), c_0_56])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, (~m1_subset_1(k15_lattice3(esk5_0,esk6_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_34]), c_0_55])]), c_0_56])).
% 0.13/0.39  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_34]), c_0_55])]), c_0_56]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 70
% 0.13/0.39  # Proof object clause steps            : 47
% 0.13/0.39  # Proof object formula steps           : 23
% 0.13/0.39  # Proof object conjectures             : 23
% 0.13/0.39  # Proof object clause conjectures      : 20
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 25
% 0.13/0.39  # Proof object initial formulas used   : 11
% 0.13/0.39  # Proof object generating inferences   : 20
% 0.13/0.39  # Proof object simplifying inferences  : 38
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 11
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 36
% 0.13/0.39  # Removed in clause preprocessing      : 1
% 0.13/0.39  # Initial clauses in saturation        : 35
% 0.13/0.39  # Processed clauses                    : 122
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 6
% 0.13/0.39  # ...remaining for further processing  : 116
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 13
% 0.13/0.39  # Backward-rewritten                   : 0
% 0.13/0.39  # Generated clauses                    : 70
% 0.13/0.39  # ...of the previous two non-trivial   : 65
% 0.13/0.39  # Contextual simplify-reflections      : 25
% 0.13/0.39  # Paramodulations                      : 69
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 1
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 68
% 0.13/0.39  #    Positive orientable unit clauses  : 5
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 3
% 0.13/0.39  #    Non-unit-clauses                  : 60
% 0.13/0.39  # Current number of unprocessed clauses: 13
% 0.13/0.39  # ...number of literals in the above   : 95
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 48
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 4254
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 215
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 44
% 0.13/0.39  # Unit Clause-clause subsumption calls : 39
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 3
% 0.13/0.39  # BW rewrite match successes           : 0
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 6658
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.040 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.044 s
% 0.13/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
