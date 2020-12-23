%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:04 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 204 expanded)
%              Number of clauses        :   49 (  78 expanded)
%              Number of leaves         :   10 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  521 (1428 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   50 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(dt_k16_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(c_0_10,plain,(
    ! [X36,X37,X38,X39,X40] :
      ( ( r3_lattice3(X36,X37,X38)
        | X37 != k16_lattice3(X36,X38)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v10_lattices(X36)
        | ~ v4_lattice3(X36)
        | ~ l3_lattices(X36) )
      & ( ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ r3_lattice3(X36,X39,X38)
        | r3_lattices(X36,X39,X37)
        | X37 != k16_lattice3(X36,X38)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v10_lattices(X36)
        | ~ v4_lattice3(X36)
        | ~ l3_lattices(X36) )
      & ( m1_subset_1(esk5_3(X36,X37,X40),u1_struct_0(X36))
        | ~ r3_lattice3(X36,X37,X40)
        | X37 = k16_lattice3(X36,X40)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v10_lattices(X36)
        | ~ v4_lattice3(X36)
        | ~ l3_lattices(X36) )
      & ( r3_lattice3(X36,esk5_3(X36,X37,X40),X40)
        | ~ r3_lattice3(X36,X37,X40)
        | X37 = k16_lattice3(X36,X40)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v10_lattices(X36)
        | ~ v4_lattice3(X36)
        | ~ l3_lattices(X36) )
      & ( ~ r3_lattices(X36,esk5_3(X36,X37,X40),X37)
        | ~ r3_lattice3(X36,X37,X40)
        | X37 = k16_lattice3(X36,X40)
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v10_lattices(X36)
        | ~ v4_lattice3(X36)
        | ~ l3_lattices(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

fof(c_0_11,plain,(
    ! [X34,X35] :
      ( v2_struct_0(X34)
      | ~ l3_lattices(X34)
      | m1_subset_1(k16_lattice3(X34,X35),u1_struct_0(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

fof(c_0_12,plain,(
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

cnf(c_0_13,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k16_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

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

cnf(c_0_17,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r3_lattice3(X1,k16_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_14])).

fof(c_0_19,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v10_lattices(esk6_0)
    & v4_lattice3(esk6_0)
    & l3_lattices(esk6_0)
    & r1_tarski(esk7_0,esk8_0)
    & ( ~ r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0))
      | ~ r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

cnf(c_0_21,plain,
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

fof(c_0_22,plain,(
    ! [X32,X33] :
      ( v2_struct_0(X32)
      | ~ l3_lattices(X32)
      | m1_subset_1(k15_lattice3(X32,X33),u1_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

cnf(c_0_23,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk2_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( r1_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_14])).

cnf(c_0_25,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
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

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | r4_lattice3(X1,X2,X3)
    | X2 != k15_lattice3(X1,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r3_lattice3(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk2_3(X1,k16_lattice3(X1,X2),X3),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk2_3(X1,k16_lattice3(X1,X2),X3),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( r4_lattice3(X1,k15_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r3_lattice3(X1,k16_lattice3(X1,esk8_0),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk2_3(X1,k16_lattice3(X1,esk8_0),X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk2_3(X1,k16_lattice3(X1,esk8_0),X2),esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk3_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( r1_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r3_lattice3(X1,k16_lattice3(X1,esk8_0),esk7_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk2_3(X1,k16_lattice3(X1,esk8_0),esk7_0),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_14])).

cnf(c_0_39,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,plain,
    ( r4_lattice3(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk3_3(X1,k15_lattice3(X1,X2),X3),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk3_3(X1,k15_lattice3(X1,X2),X3),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_29])).

cnf(c_0_41,plain,
    ( r3_lattices(X2,X1,X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_lattice3(X2,X1,X3)
    | X4 != k16_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( r3_lattice3(X1,k16_lattice3(X1,esk8_0),esk7_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_14])).

fof(c_0_43,plain,(
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

fof(c_0_44,plain,(
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

cnf(c_0_45,negated_conjecture,
    ( r4_lattice3(X1,k15_lattice3(X1,esk8_0),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk3_3(X1,k15_lattice3(X1,esk8_0),X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk3_3(X1,k15_lattice3(X1,esk8_0),X2),esk7_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_31])).

cnf(c_0_46,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( ~ r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0))
    | ~ r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( r3_lattices(X1,k16_lattice3(X1,esk8_0),X2)
    | v2_struct_0(X1)
    | X2 != k16_lattice3(X1,esk7_0)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_14])).

cnf(c_0_49,negated_conjecture,
    ( v4_lattice3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( v10_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_51,negated_conjecture,
    ( l3_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_53,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_57,plain,
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

cnf(c_0_58,negated_conjecture,
    ( r4_lattice3(X1,k15_lattice3(X1,esk8_0),esk7_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk3_3(X1,k15_lattice3(X1,esk8_0),esk7_0),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_29])).

cnf(c_0_59,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_60,negated_conjecture,
    ( ~ r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0))
    | ~ m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_51])]),c_0_52])).

cnf(c_0_61,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56])).

cnf(c_0_62,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r4_lattice3(X1,k15_lattice3(X1,esk8_0),esk7_0)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_29])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0))
    | ~ m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ m1_subset_1(k15_lattice3(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ m1_subset_1(k15_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_50]),c_0_51])]),c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( r1_lattices(X1,X2,k15_lattice3(X1,esk8_0))
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,esk7_0)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_29])).

cnf(c_0_66,negated_conjecture,
    ( ~ m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ m1_subset_1(k15_lattice3(esk6_0,esk8_0),u1_struct_0(esk6_0))
    | ~ m1_subset_1(k15_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_49]),c_0_50]),c_0_51])]),c_0_52])).

cnf(c_0_67,negated_conjecture,
    ( ~ m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0))
    | ~ m1_subset_1(k15_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_29]),c_0_51])]),c_0_52])).

cnf(c_0_68,negated_conjecture,
    ( ~ m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_29]),c_0_51])]),c_0_52])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_14]),c_0_51])]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.20/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.030 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 0.20/0.39  fof(dt_k16_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 0.20/0.39  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 0.20/0.39  fof(t46_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_lattice3)).
% 0.20/0.39  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 0.20/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.39  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.20/0.39  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 0.20/0.39  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.20/0.39  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.20/0.39  fof(c_0_10, plain, ![X36, X37, X38, X39, X40]:(((r3_lattice3(X36,X37,X38)|X37!=k16_lattice3(X36,X38)|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~v10_lattices(X36)|~v4_lattice3(X36)|~l3_lattices(X36)))&(~m1_subset_1(X39,u1_struct_0(X36))|(~r3_lattice3(X36,X39,X38)|r3_lattices(X36,X39,X37))|X37!=k16_lattice3(X36,X38)|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~v10_lattices(X36)|~v4_lattice3(X36)|~l3_lattices(X36))))&((m1_subset_1(esk5_3(X36,X37,X40),u1_struct_0(X36))|~r3_lattice3(X36,X37,X40)|X37=k16_lattice3(X36,X40)|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~v10_lattices(X36)|~v4_lattice3(X36)|~l3_lattices(X36)))&((r3_lattice3(X36,esk5_3(X36,X37,X40),X40)|~r3_lattice3(X36,X37,X40)|X37=k16_lattice3(X36,X40)|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~v10_lattices(X36)|~v4_lattice3(X36)|~l3_lattices(X36)))&(~r3_lattices(X36,esk5_3(X36,X37,X40),X37)|~r3_lattice3(X36,X37,X40)|X37=k16_lattice3(X36,X40)|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~v10_lattices(X36)|~v4_lattice3(X36)|~l3_lattices(X36)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.20/0.39  fof(c_0_11, plain, ![X34, X35]:(v2_struct_0(X34)|~l3_lattices(X34)|m1_subset_1(k16_lattice3(X34,X35),u1_struct_0(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).
% 0.20/0.39  fof(c_0_12, plain, ![X15, X16, X17, X18, X19]:((~r3_lattice3(X15,X16,X17)|(~m1_subset_1(X18,u1_struct_0(X15))|(~r2_hidden(X18,X17)|r1_lattices(X15,X16,X18)))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&((m1_subset_1(esk2_3(X15,X16,X19),u1_struct_0(X15))|r3_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&((r2_hidden(esk2_3(X15,X16,X19),X19)|r3_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))&(~r1_lattices(X15,X16,esk2_3(X15,X16,X19))|r3_lattice3(X15,X16,X19)|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l3_lattices(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.20/0.39  cnf(c_0_13, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|X2!=k16_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_14, plain, (v2_struct_0(X1)|m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  fof(c_0_15, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2)))))), inference(assume_negation,[status(cth)],[t46_lattice3])).
% 0.20/0.39  fof(c_0_16, plain, ![X27, X28, X29, X30]:(((r4_lattice3(X27,X29,X28)|X29!=k15_lattice3(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27))|(v2_struct_0(X27)|~l3_lattices(X27)))&(~m1_subset_1(X30,u1_struct_0(X27))|(~r4_lattice3(X27,X30,X28)|r1_lattices(X27,X29,X30))|X29!=k15_lattice3(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27))|(v2_struct_0(X27)|~l3_lattices(X27))))&((m1_subset_1(esk4_3(X27,X28,X29),u1_struct_0(X27))|~r4_lattice3(X27,X29,X28)|X29=k15_lattice3(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27))|(v2_struct_0(X27)|~l3_lattices(X27)))&((r4_lattice3(X27,esk4_3(X27,X28,X29),X28)|~r4_lattice3(X27,X29,X28)|X29=k15_lattice3(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27))|(v2_struct_0(X27)|~l3_lattices(X27)))&(~r1_lattices(X27,X29,esk4_3(X27,X28,X29))|~r4_lattice3(X27,X29,X28)|X29=k15_lattice3(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27))|(v2_struct_0(X27)|~l3_lattices(X27)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.20/0.39  cnf(c_0_17, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_18, plain, (r3_lattice3(X1,k16_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]), c_0_14])).
% 0.20/0.39  fof(c_0_19, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.39  fof(c_0_20, negated_conjecture, ((((~v2_struct_0(esk6_0)&v10_lattices(esk6_0))&v4_lattice3(esk6_0))&l3_lattices(esk6_0))&(r1_tarski(esk7_0,esk8_0)&(~r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0))|~r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.20/0.39  cnf(c_0_21, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X1)|X2!=k15_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  fof(c_0_22, plain, ![X32, X33]:(v2_struct_0(X32)|~l3_lattices(X32)|m1_subset_1(k15_lattice3(X32,X33),u1_struct_0(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.20/0.39  cnf(c_0_23, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk2_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_24, plain, (r1_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_14])).
% 0.20/0.39  cnf(c_0_25, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (r1_tarski(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  fof(c_0_27, plain, ![X21, X22, X23, X24, X25]:((~r4_lattice3(X21,X22,X23)|(~m1_subset_1(X24,u1_struct_0(X21))|(~r2_hidden(X24,X23)|r1_lattices(X21,X24,X22)))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&((m1_subset_1(esk3_3(X21,X22,X25),u1_struct_0(X21))|r4_lattice3(X21,X22,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&((r2_hidden(esk3_3(X21,X22,X25),X25)|r4_lattice3(X21,X22,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&(~r1_lattices(X21,esk3_3(X21,X22,X25),X22)|r4_lattice3(X21,X22,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.20/0.39  cnf(c_0_28, plain, (v2_struct_0(X1)|r4_lattice3(X1,X2,X3)|X2!=k15_lattice3(X1,X3)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_29, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.39  cnf(c_0_30, plain, (r3_lattice3(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk2_3(X1,k16_lattice3(X1,X2),X3),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(esk2_3(X1,k16_lattice3(X1,X2),X3),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_14])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.39  cnf(c_0_32, plain, (r1_lattices(X1,X4,X2)|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_33, plain, (r4_lattice3(X1,k15_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]), c_0_29])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, (r3_lattice3(X1,k16_lattice3(X1,esk8_0),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk2_3(X1,k16_lattice3(X1,esk8_0),X2),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(esk2_3(X1,k16_lattice3(X1,esk8_0),X2),esk7_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.39  cnf(c_0_35, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_36, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk3_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_37, plain, (r1_lattices(X1,X2,k15_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_29])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (r3_lattice3(X1,k16_lattice3(X1,esk8_0),esk7_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk2_3(X1,k16_lattice3(X1,esk8_0),esk7_0),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_14])).
% 0.20/0.39  cnf(c_0_39, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_40, plain, (r4_lattice3(X1,k15_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk3_3(X1,k15_lattice3(X1,X2),X3),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(esk3_3(X1,k15_lattice3(X1,X2),X3),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_29])).
% 0.20/0.39  cnf(c_0_41, plain, (r3_lattices(X2,X1,X4)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_lattice3(X2,X1,X3)|X4!=k16_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (r3_lattice3(X1,k16_lattice3(X1,esk8_0),esk7_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_14])).
% 0.20/0.39  fof(c_0_43, plain, ![X12, X13, X14]:((~r3_lattices(X12,X13,X14)|r1_lattices(X12,X13,X14)|(v2_struct_0(X12)|~v6_lattices(X12)|~v8_lattices(X12)|~v9_lattices(X12)|~l3_lattices(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))))&(~r1_lattices(X12,X13,X14)|r3_lattices(X12,X13,X14)|(v2_struct_0(X12)|~v6_lattices(X12)|~v8_lattices(X12)|~v9_lattices(X12)|~l3_lattices(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.20/0.39  fof(c_0_44, plain, ![X11]:(((((((~v2_struct_0(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11))&(v4_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11)))&(v5_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11)))&(v6_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11)))&(v7_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11)))&(v8_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11)))&(v9_lattices(X11)|(v2_struct_0(X11)|~v10_lattices(X11))|~l3_lattices(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, (r4_lattice3(X1,k15_lattice3(X1,esk8_0),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk3_3(X1,k15_lattice3(X1,esk8_0),X2),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(esk3_3(X1,k15_lattice3(X1,esk8_0),X2),esk7_0)), inference(spm,[status(thm)],[c_0_40, c_0_31])).
% 0.20/0.39  cnf(c_0_46, plain, (r2_hidden(esk3_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (~r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0))|~r3_lattices(esk6_0,k16_lattice3(esk6_0,esk8_0),k16_lattice3(esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (r3_lattices(X1,k16_lattice3(X1,esk8_0),X2)|v2_struct_0(X1)|X2!=k16_lattice3(X1,esk7_0)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_14])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (v4_lattice3(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_50, negated_conjecture, (v10_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, (l3_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_53, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.39  cnf(c_0_54, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.39  cnf(c_0_55, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.39  cnf(c_0_56, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.39  cnf(c_0_57, plain, (r1_lattices(X2,X4,X1)|v2_struct_0(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r4_lattice3(X2,X1,X3)|X4!=k15_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, (r4_lattice3(X1,k15_lattice3(X1,esk8_0),esk7_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk3_3(X1,k15_lattice3(X1,esk8_0),esk7_0),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_29])).
% 0.20/0.39  cnf(c_0_59, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (~r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0))|~m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50]), c_0_51])]), c_0_52])).
% 0.20/0.39  cnf(c_0_61, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56])).
% 0.20/0.39  cnf(c_0_62, plain, (v2_struct_0(X2)|r1_lattices(X2,X4,X1)|X4!=k15_lattice3(X2,X3)|~l3_lattices(X2)|~v10_lattices(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))), inference(cn,[status(thm)],[c_0_57])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (r4_lattice3(X1,k15_lattice3(X1,esk8_0),esk7_0)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_29])).
% 0.20/0.39  cnf(c_0_64, negated_conjecture, (~r1_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0))|~m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0))|~m1_subset_1(k15_lattice3(esk6_0,esk8_0),u1_struct_0(esk6_0))|~m1_subset_1(k15_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_50]), c_0_51])]), c_0_52])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (r1_lattices(X1,X2,k15_lattice3(X1,esk8_0))|v2_struct_0(X1)|X2!=k15_lattice3(X1,esk7_0)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_29])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (~m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0))|~m1_subset_1(k15_lattice3(esk6_0,esk8_0),u1_struct_0(esk6_0))|~m1_subset_1(k15_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_49]), c_0_50]), c_0_51])]), c_0_52])).
% 0.20/0.39  cnf(c_0_67, negated_conjecture, (~m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0))|~m1_subset_1(k15_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_29]), c_0_51])]), c_0_52])).
% 0.20/0.39  cnf(c_0_68, negated_conjecture, (~m1_subset_1(k16_lattice3(esk6_0,esk7_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_29]), c_0_51])]), c_0_52])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_14]), c_0_51])]), c_0_52]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 70
% 0.20/0.39  # Proof object clause steps            : 49
% 0.20/0.39  # Proof object formula steps           : 21
% 0.20/0.39  # Proof object conjectures             : 24
% 0.20/0.39  # Proof object clause conjectures      : 21
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 25
% 0.20/0.39  # Proof object initial formulas used   : 10
% 0.20/0.39  # Proof object generating inferences   : 22
% 0.20/0.39  # Proof object simplifying inferences  : 39
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 11
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 39
% 0.20/0.39  # Removed in clause preprocessing      : 1
% 0.20/0.39  # Initial clauses in saturation        : 38
% 0.20/0.39  # Processed clauses                    : 164
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 9
% 0.20/0.39  # ...remaining for further processing  : 155
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 35
% 0.20/0.39  # Backward-rewritten                   : 0
% 0.20/0.39  # Generated clauses                    : 118
% 0.20/0.39  # ...of the previous two non-trivial   : 112
% 0.20/0.39  # Contextual simplify-reflections      : 42
% 0.20/0.39  # Paramodulations                      : 116
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 2
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 82
% 0.20/0.39  #    Positive orientable unit clauses  : 5
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 2
% 0.20/0.39  #    Non-unit-clauses                  : 75
% 0.20/0.39  # Current number of unprocessed clauses: 23
% 0.20/0.39  # ...number of literals in the above   : 219
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 73
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 7171
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 278
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 86
% 0.20/0.39  # Unit Clause-clause subsumption calls : 38
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 3
% 0.20/0.39  # BW rewrite match successes           : 0
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 9107
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.047 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.051 s
% 0.20/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
