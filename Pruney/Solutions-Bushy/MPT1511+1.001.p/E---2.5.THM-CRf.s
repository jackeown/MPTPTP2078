%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1511+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:19 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 298 expanded)
%              Number of clauses        :   48 ( 103 expanded)
%              Number of leaves         :   10 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  517 (2287 expanded)
%              Number of equality atoms :   27 ( 303 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal clause size      :   30 (   5 average)
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

fof(fraenkel_a_2_4_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v4_lattice3(X2)
        & l3_lattices(X2)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( r2_hidden(X1,a_2_4_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & r3_lattices(X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_4_lattice3)).

fof(t45_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( X2 = k15_lattice3(X1,a_2_3_lattice3(X1,X2))
            & X2 = k16_lattice3(X1,a_2_4_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).

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

fof(fraenkel_a_2_3_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v4_lattice3(X2)
        & l3_lattices(X2)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( r2_hidden(X1,a_2_3_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & r3_lattices(X2,X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_3_lattice3)).

fof(reflexivity_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_lattices(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

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

fof(t42_lattice3,axiom,(
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

fof(c_0_10,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r3_lattices(X28,X29,X30)
        | r1_lattices(X28,X29,X30)
        | v2_struct_0(X28)
        | ~ v6_lattices(X28)
        | ~ v8_lattices(X28)
        | ~ v9_lattices(X28)
        | ~ l3_lattices(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ m1_subset_1(X30,u1_struct_0(X28)) )
      & ( ~ r1_lattices(X28,X29,X30)
        | r3_lattices(X28,X29,X30)
        | v2_struct_0(X28)
        | ~ v6_lattices(X28)
        | ~ v8_lattices(X28)
        | ~ v9_lattices(X28)
        | ~ l3_lattices(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ m1_subset_1(X30,u1_struct_0(X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

fof(c_0_11,plain,(
    ! [X5] :
      ( ( ~ v2_struct_0(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v4_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v5_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v6_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v7_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v8_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v9_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_12,plain,(
    ! [X23,X24,X25,X27] :
      ( ( m1_subset_1(esk4_3(X23,X24,X25),u1_struct_0(X24))
        | ~ r2_hidden(X23,a_2_4_lattice3(X24,X25))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24)) )
      & ( X23 = esk4_3(X23,X24,X25)
        | ~ r2_hidden(X23,a_2_4_lattice3(X24,X25))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24)) )
      & ( r3_lattices(X24,X25,esk4_3(X23,X24,X25))
        | ~ r2_hidden(X23,a_2_4_lattice3(X24,X25))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24)) )
      & ( ~ m1_subset_1(X27,u1_struct_0(X24))
        | X23 != X27
        | ~ r3_lattices(X24,X25,X27)
        | r2_hidden(X23,a_2_4_lattice3(X24,X25))
        | v2_struct_0(X24)
        | ~ v10_lattices(X24)
        | ~ v4_lattice3(X24)
        | ~ l3_lattices(X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_4_lattice3])])])])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( X2 = k15_lattice3(X1,a_2_3_lattice3(X1,X2))
              & X2 = k16_lattice3(X1,a_2_4_lattice3(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t45_lattice3])).

fof(c_0_14,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r3_lattice3(X6,X7,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | ~ r2_hidden(X9,X8)
        | r1_lattices(X6,X7,X9)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) )
      & ( m1_subset_1(esk1_3(X6,X7,X10),u1_struct_0(X6))
        | r3_lattice3(X6,X7,X10)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) )
      & ( r2_hidden(esk1_3(X6,X7,X10),X10)
        | r3_lattice3(X6,X7,X10)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) )
      & ( ~ r1_lattices(X6,X7,esk1_3(X6,X7,X10))
        | r3_lattice3(X6,X7,X10)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

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
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r3_lattices(X1,X2,esk4_3(X3,X1,X2))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,a_2_4_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( X1 = esk4_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_4_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X18,X19,X20,X22] :
      ( ( m1_subset_1(esk3_3(X18,X19,X20),u1_struct_0(X19))
        | ~ r2_hidden(X18,a_2_3_lattice3(X19,X20))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19)) )
      & ( X18 = esk3_3(X18,X19,X20)
        | ~ r2_hidden(X18,a_2_3_lattice3(X19,X20))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19)) )
      & ( r3_lattices(X19,esk3_3(X18,X19,X20),X20)
        | ~ r2_hidden(X18,a_2_3_lattice3(X19,X20))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19)) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X19))
        | X18 != X22
        | ~ r3_lattices(X19,X22,X20)
        | r2_hidden(X18,a_2_3_lattice3(X19,X20))
        | v2_struct_0(X19)
        | ~ v10_lattices(X19)
        | ~ v4_lattice3(X19)
        | ~ l3_lattices(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_3_lattice3])])])])])])).

fof(c_0_22,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ v6_lattices(X31)
      | ~ v8_lattices(X31)
      | ~ v9_lattices(X31)
      | ~ l3_lattices(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | ~ m1_subset_1(X33,u1_struct_0(X31))
      | r3_lattices(X31,X32,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_lattices])])])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v10_lattices(esk5_0)
    & v4_lattice3(esk5_0)
    & l3_lattices(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & ( esk6_0 != k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,esk6_0))
      | esk6_0 != k16_lattice3(esk5_0,a_2_4_lattice3(esk5_0,esk6_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

cnf(c_0_24,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X3,a_2_4_lattice3(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_29,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r4_lattice3(X12,X13,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r2_hidden(X15,X14)
        | r1_lattices(X12,X15,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk2_3(X12,X13,X16),u1_struct_0(X12))
        | r4_lattice3(X12,X13,X16)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( r2_hidden(esk2_3(X12,X13,X16),X16)
        | r4_lattice3(X12,X13,X16)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( ~ r1_lattices(X12,esk2_3(X12,X13,X16),X13)
        | r4_lattice3(X12,X13,X16)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

cnf(c_0_30,plain,
    ( r3_lattices(X1,esk3_3(X2,X1,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_3_lattice3(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( X1 = esk3_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_3_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,X2,X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( l3_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_36,plain,(
    ! [X37,X38,X39] :
      ( v2_struct_0(X37)
      | ~ v10_lattices(X37)
      | ~ v4_lattice3(X37)
      | ~ l3_lattices(X37)
      | ~ m1_subset_1(X38,u1_struct_0(X37))
      | ~ r2_hidden(X38,X39)
      | ~ r3_lattice3(X37,X38,X39)
      | k16_lattice3(X37,X39) = X38 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_lattice3])])])])).

cnf(c_0_37,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_38,plain,
    ( r3_lattices(X1,X2,esk1_3(X3,X4,a_2_4_lattice3(X1,X2)))
    | r3_lattice3(X3,X4,a_2_4_lattice3(X1,X2))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk2_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X2,a_2_3_lattice3(X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_42,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( r3_lattices(esk5_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( v10_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | k16_lattice3(X1,X3) = X2
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X3)
    | ~ r3_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( r3_lattice3(X1,X2,a_2_4_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_47,plain,(
    ! [X34,X35,X36] :
      ( v2_struct_0(X34)
      | ~ v10_lattices(X34)
      | ~ v4_lattice3(X34)
      | ~ l3_lattices(X34)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | ~ r2_hidden(X35,X36)
      | ~ r4_lattice3(X34,X35,X36)
      | k15_lattice3(X34,X36) = X35 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_lattice3])])])])).

cnf(c_0_48,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,esk2_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_25]),c_0_40])).

cnf(c_0_49,plain,
    ( r3_lattices(X1,esk2_3(X2,X3,a_2_3_lattice3(X1,X4)),X4)
    | r4_lattice3(X2,X3,a_2_3_lattice3(X1,X4))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r3_lattices(esk5_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_16]),c_0_44]),c_0_34])]),c_0_35])).

cnf(c_0_51,negated_conjecture,
    ( esk6_0 != k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,esk6_0))
    | esk6_0 != k16_lattice3(esk5_0,a_2_4_lattice3(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_52,plain,
    ( k16_lattice3(X1,a_2_4_lattice3(X1,X2)) = X2
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X2,a_2_4_lattice3(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( v4_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X3) = X2
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X3)
    | ~ r4_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( r4_lattice3(X1,X2,a_2_3_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( r2_hidden(X3,a_2_4_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattices(X2,X4,X1)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_57,negated_conjecture,
    ( r3_lattices(esk5_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_18]),c_0_44]),c_0_34])]),c_0_35])).

cnf(c_0_58,negated_conjecture,
    ( k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,esk6_0)) != esk6_0
    | ~ r2_hidden(esk6_0,a_2_4_lattice3(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_33]),c_0_44]),c_0_34])]),c_0_35])).

cnf(c_0_59,plain,
    ( k15_lattice3(X1,a_2_3_lattice3(X1,X2)) = X2
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X2,a_2_3_lattice3(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,a_2_4_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattices(X2,X3,X1)
    | ~ v4_lattice3(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r3_lattices(esk5_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_17]),c_0_44]),c_0_34])]),c_0_35])).

cnf(c_0_62,plain,
    ( r2_hidden(X3,a_2_3_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattices(X2,X1,X4)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(esk6_0,a_2_4_lattice3(esk5_0,esk6_0))
    | ~ r2_hidden(esk6_0,a_2_3_lattice3(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_53]),c_0_33]),c_0_44]),c_0_34])]),c_0_35])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(X1,a_2_4_lattice3(esk5_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_53]),c_0_44]),c_0_34])]),c_0_35])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,a_2_3_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattices(X2,X1,X3)
    | ~ v4_lattice3(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(esk6_0,a_2_3_lattice3(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_33])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(X1,a_2_3_lattice3(esk5_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_61]),c_0_53]),c_0_44]),c_0_34])]),c_0_35])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_33])]),
    [proof]).

%------------------------------------------------------------------------------
