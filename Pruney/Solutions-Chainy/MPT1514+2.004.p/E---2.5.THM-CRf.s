%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:05 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   82 (1383 expanded)
%              Number of clauses        :   57 ( 459 expanded)
%              Number of leaves         :   12 ( 336 expanded)
%              Depth                    :   19
%              Number of atoms          :  529 (10944 expanded)
%              Number of equality atoms :   37 ( 113 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   40 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2,X3] :
          ( ! [X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ~ ( r2_hidden(X4,X2)
                  & ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X1))
                     => ~ ( r3_lattices(X1,X4,X5)
                          & r2_hidden(X5,X3) ) ) ) )
         => r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

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

fof(t37_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] : k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

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

fof(t45_lattice3,axiom,(
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

fof(fraenkel_a_2_5_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v4_lattice3(X2)
        & l3_lattices(X2) )
     => ( r2_hidden(X1,a_2_5_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ? [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
                & r3_lattices(X2,X4,X5)
                & r2_hidden(X5,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).

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

fof(t47_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( k15_lattice3(X1,X2) = k15_lattice3(X1,a_2_5_lattice3(X1,X2))
          & k16_lattice3(X1,X2) = k16_lattice3(X1,a_2_6_lattice3(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).

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

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2,X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ~ ( r2_hidden(X4,X2)
                    & ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ~ ( r3_lattices(X1,X4,X5)
                            & r2_hidden(X5,X3) ) ) ) )
           => r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t48_lattice3])).

fof(c_0_13,negated_conjecture,(
    ! [X57] :
      ( ~ v2_struct_0(esk8_0)
      & v10_lattices(esk8_0)
      & v4_lattice3(esk8_0)
      & l3_lattices(esk8_0)
      & ( m1_subset_1(esk11_1(X57),u1_struct_0(esk8_0))
        | ~ r2_hidden(X57,esk9_0)
        | ~ m1_subset_1(X57,u1_struct_0(esk8_0)) )
      & ( r3_lattices(esk8_0,X57,esk11_1(X57))
        | ~ r2_hidden(X57,esk9_0)
        | ~ m1_subset_1(X57,u1_struct_0(esk8_0)) )
      & ( r2_hidden(esk11_1(X57),esk10_0)
        | ~ r2_hidden(X57,esk9_0)
        | ~ m1_subset_1(X57,u1_struct_0(esk8_0)) )
      & ~ r3_lattices(esk8_0,k15_lattice3(esk8_0,esk9_0),k15_lattice3(esk8_0,esk10_0)) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).

fof(c_0_14,plain,(
    ! [X18,X19] :
      ( v2_struct_0(X18)
      | ~ l3_lattices(X18)
      | m1_subset_1(k15_lattice3(X18,X19),u1_struct_0(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_15,plain,(
    ! [X20,X21,X22,X24,X25] :
      ( ( m1_subset_1(esk3_3(X20,X21,X22),u1_struct_0(X21))
        | ~ r2_hidden(X20,a_2_2_lattice3(X21,X22))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v4_lattice3(X21)
        | ~ l3_lattices(X21) )
      & ( X20 = esk3_3(X20,X21,X22)
        | ~ r2_hidden(X20,a_2_2_lattice3(X21,X22))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v4_lattice3(X21)
        | ~ l3_lattices(X21) )
      & ( r4_lattice3(X21,esk3_3(X20,X21,X22),X22)
        | ~ r2_hidden(X20,a_2_2_lattice3(X21,X22))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v4_lattice3(X21)
        | ~ l3_lattices(X21) )
      & ( ~ m1_subset_1(X25,u1_struct_0(X21))
        | X20 != X25
        | ~ r4_lattice3(X21,X25,X24)
        | r2_hidden(X20,a_2_2_lattice3(X21,X24))
        | v2_struct_0(X21)
        | ~ v10_lattices(X21)
        | ~ v4_lattice3(X21)
        | ~ l3_lattices(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).

fof(c_0_16,plain,(
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

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( l3_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X47,X48,X49] :
      ( ( r3_lattices(X47,X48,k15_lattice3(X47,X49))
        | ~ r2_hidden(X48,X49)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | v2_struct_0(X47)
        | ~ v10_lattices(X47)
        | ~ v4_lattice3(X47)
        | ~ l3_lattices(X47) )
      & ( r3_lattices(X47,k16_lattice3(X47,X49),X48)
        | ~ r2_hidden(X48,X49)
        | ~ m1_subset_1(X48,u1_struct_0(X47))
        | v2_struct_0(X47)
        | ~ v10_lattices(X47)
        | ~ v4_lattice3(X47)
        | ~ l3_lattices(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,a_2_2_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r4_lattice3(X2,X1,X4)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk8_0,X1),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

fof(c_0_24,plain,(
    ! [X45,X46] :
      ( v2_struct_0(X45)
      | ~ v10_lattices(X45)
      | ~ v4_lattice3(X45)
      | ~ l3_lattices(X45)
      | k15_lattice3(X45,X46) = k16_lattice3(X45,a_2_2_lattice3(X45,X46)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).

cnf(c_0_25,plain,
    ( r3_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v4_lattice3(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( v10_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r4_lattice3(esk8_0,k15_lattice3(esk8_0,X1),X2)
    | m1_subset_1(esk2_3(esk8_0,k15_lattice3(esk8_0,X1),X2),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_19])]),c_0_17])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r3_lattices(esk8_0,k16_lattice3(esk8_0,X1),k15_lattice3(esk8_0,X2))
    | ~ r2_hidden(k15_lattice3(esk8_0,X2),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_26]),c_0_27]),c_0_19])]),c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2))
    | m1_subset_1(esk2_3(esk8_0,k15_lattice3(esk8_0,X1),X2),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_26]),c_0_27]),c_0_23]),c_0_19])]),c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_27]),c_0_19])]),c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( ~ r3_lattices(esk8_0,k15_lattice3(esk8_0,esk9_0),k15_lattice3(esk8_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( r3_lattices(esk8_0,k15_lattice3(esk8_0,X1),k15_lattice3(esk8_0,X2))
    | m1_subset_1(esk2_3(esk8_0,k15_lattice3(esk8_0,X2),X1),u1_struct_0(esk8_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_36,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk11_1(X1),u1_struct_0(esk8_0))
    | ~ r2_hidden(X1,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( r4_lattice3(esk8_0,k15_lattice3(esk8_0,X1),X2)
    | r2_hidden(esk2_3(esk8_0,k15_lattice3(esk8_0,X1),X2),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_23]),c_0_19])]),c_0_17])).

fof(c_0_40,plain,(
    ! [X39,X40,X41,X42,X43] :
      ( ( r3_lattice3(X39,X40,X41)
        | X40 != k16_lattice3(X39,X41)
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | v2_struct_0(X39)
        | ~ v10_lattices(X39)
        | ~ v4_lattice3(X39)
        | ~ l3_lattices(X39) )
      & ( ~ m1_subset_1(X42,u1_struct_0(X39))
        | ~ r3_lattice3(X39,X42,X41)
        | r3_lattices(X39,X42,X40)
        | X40 != k16_lattice3(X39,X41)
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | v2_struct_0(X39)
        | ~ v10_lattices(X39)
        | ~ v4_lattice3(X39)
        | ~ l3_lattices(X39) )
      & ( m1_subset_1(esk7_3(X39,X40,X43),u1_struct_0(X39))
        | ~ r3_lattice3(X39,X40,X43)
        | X40 = k16_lattice3(X39,X43)
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | v2_struct_0(X39)
        | ~ v10_lattices(X39)
        | ~ v4_lattice3(X39)
        | ~ l3_lattices(X39) )
      & ( r3_lattice3(X39,esk7_3(X39,X40,X43),X43)
        | ~ r3_lattice3(X39,X40,X43)
        | X40 = k16_lattice3(X39,X43)
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | v2_struct_0(X39)
        | ~ v10_lattices(X39)
        | ~ v4_lattice3(X39)
        | ~ l3_lattices(X39) )
      & ( ~ r3_lattices(X39,esk7_3(X39,X40,X43),X40)
        | ~ r3_lattice3(X39,X40,X43)
        | X40 = k16_lattice3(X39,X43)
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | v2_struct_0(X39)
        | ~ v10_lattices(X39)
        | ~ v4_lattice3(X39)
        | ~ l3_lattices(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

fof(c_0_41,plain,(
    ! [X50,X51] :
      ( ( X51 = k15_lattice3(X50,a_2_3_lattice3(X50,X51))
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50) )
      & ( X51 = k16_lattice3(X50,a_2_4_lattice3(X50,X51))
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).

fof(c_0_42,plain,(
    ! [X31,X32,X33,X36,X37,X38] :
      ( ( m1_subset_1(esk5_3(X31,X32,X33),u1_struct_0(X32))
        | ~ r2_hidden(X31,a_2_5_lattice3(X32,X33))
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ v4_lattice3(X32)
        | ~ l3_lattices(X32) )
      & ( X31 = esk5_3(X31,X32,X33)
        | ~ r2_hidden(X31,a_2_5_lattice3(X32,X33))
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ v4_lattice3(X32)
        | ~ l3_lattices(X32) )
      & ( m1_subset_1(esk6_3(X31,X32,X33),u1_struct_0(X32))
        | ~ r2_hidden(X31,a_2_5_lattice3(X32,X33))
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ v4_lattice3(X32)
        | ~ l3_lattices(X32) )
      & ( r3_lattices(X32,esk5_3(X31,X32,X33),esk6_3(X31,X32,X33))
        | ~ r2_hidden(X31,a_2_5_lattice3(X32,X33))
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ v4_lattice3(X32)
        | ~ l3_lattices(X32) )
      & ( r2_hidden(esk6_3(X31,X32,X33),X33)
        | ~ r2_hidden(X31,a_2_5_lattice3(X32,X33))
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ v4_lattice3(X32)
        | ~ l3_lattices(X32) )
      & ( ~ m1_subset_1(X37,u1_struct_0(X32))
        | X31 != X37
        | ~ m1_subset_1(X38,u1_struct_0(X32))
        | ~ r3_lattices(X32,X37,X38)
        | ~ r2_hidden(X38,X36)
        | r2_hidden(X31,a_2_5_lattice3(X32,X36))
        | v2_struct_0(X32)
        | ~ v10_lattices(X32)
        | ~ v4_lattice3(X32)
        | ~ l3_lattices(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_5_lattice3])])])])])])])).

cnf(c_0_43,negated_conjecture,
    ( r3_lattices(esk8_0,X1,esk11_1(X1))
    | ~ r2_hidden(X1,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk11_1(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)),u1_struct_0(esk8_0))
    | ~ r2_hidden(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,k15_lattice3(esk8_0,X1),X2),X2)
    | r2_hidden(k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_39]),c_0_26]),c_0_27]),c_0_23]),c_0_19])]),c_0_17])).

cnf(c_0_46,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k16_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( X1 = k16_lattice3(X2,a_2_4_lattice3(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(X3,a_2_5_lattice3(X2,X5))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r3_lattices(X2,X1,X4)
    | ~ r2_hidden(X4,X5)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r3_lattices(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),esk11_1(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)))
    | ~ r2_hidden(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0))
    | m1_subset_1(esk11_1(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_51,plain,(
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

cnf(c_0_52,plain,
    ( r3_lattice3(X1,k16_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_4_lattice3(esk8_0,k15_lattice3(esk8_0,X1))) = k15_lattice3(esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_23]),c_0_26]),c_0_27]),c_0_19])]),c_0_17])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,a_2_5_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattices(X2,X1,X4)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( r3_lattices(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),esk11_1(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)))
    | r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk11_1(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_50]),c_0_33]),c_0_34])).

fof(c_0_57,plain,(
    ! [X52,X53] :
      ( ( k15_lattice3(X52,X53) = k15_lattice3(X52,a_2_5_lattice3(X52,X53))
        | v2_struct_0(X52)
        | ~ v10_lattices(X52)
        | ~ v4_lattice3(X52)
        | ~ l3_lattices(X52) )
      & ( k16_lattice3(X52,X53) = k16_lattice3(X52,a_2_6_lattice3(X52,X53))
        | v2_struct_0(X52)
        | ~ v10_lattices(X52)
        | ~ v4_lattice3(X52)
        | ~ l3_lattices(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).

cnf(c_0_58,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),a_2_4_lattice3(esk8_0,k15_lattice3(esk8_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_26]),c_0_27]),c_0_23]),c_0_19])]),c_0_17])).

fof(c_0_60,plain,(
    ! [X26,X27,X28,X30] :
      ( ( m1_subset_1(esk4_3(X26,X27,X28),u1_struct_0(X27))
        | ~ r2_hidden(X26,a_2_4_lattice3(X27,X28))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ v4_lattice3(X27)
        | ~ l3_lattices(X27)
        | ~ m1_subset_1(X28,u1_struct_0(X27)) )
      & ( X26 = esk4_3(X26,X27,X28)
        | ~ r2_hidden(X26,a_2_4_lattice3(X27,X28))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ v4_lattice3(X27)
        | ~ l3_lattices(X27)
        | ~ m1_subset_1(X28,u1_struct_0(X27)) )
      & ( r3_lattices(X27,X28,esk4_3(X26,X27,X28))
        | ~ r2_hidden(X26,a_2_4_lattice3(X27,X28))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ v4_lattice3(X27)
        | ~ l3_lattices(X27)
        | ~ m1_subset_1(X28,u1_struct_0(X27)) )
      & ( ~ m1_subset_1(X30,u1_struct_0(X27))
        | X26 != X30
        | ~ r3_lattices(X27,X28,X30)
        | r2_hidden(X26,a_2_4_lattice3(X27,X28))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ v4_lattice3(X27)
        | ~ l3_lattices(X27)
        | ~ m1_subset_1(X28,u1_struct_0(X27)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_4_lattice3])])])])])])).

cnf(c_0_61,plain,
    ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),a_2_5_lattice3(esk8_0,X1))
    | r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0))
    | ~ r2_hidden(esk11_1(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_26]),c_0_27]),c_0_56]),c_0_38]),c_0_19])]),c_0_17])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk11_1(X1),esk10_0)
    | ~ r2_hidden(X1,esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_64,plain,
    ( k15_lattice3(X1,X2) = k15_lattice3(X1,a_2_5_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( r1_lattices(esk8_0,k15_lattice3(esk8_0,X1),X2)
    | ~ r2_hidden(X2,a_2_4_lattice3(esk8_0,k15_lattice3(esk8_0,X1)))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_23]),c_0_19])]),c_0_17])).

cnf(c_0_66,plain,
    ( X1 = k15_lattice3(X2,a_2_3_lattice3(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_67,plain,
    ( r2_hidden(X3,a_2_4_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattices(X2,X4,X1)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( r3_lattices(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),k15_lattice3(esk8_0,X1))
    | ~ r2_hidden(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_38]),c_0_26]),c_0_27]),c_0_19])]),c_0_17])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),a_2_5_lattice3(esk8_0,esk10_0))
    | r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_38])]),c_0_45])).

cnf(c_0_70,negated_conjecture,
    ( k15_lattice3(esk8_0,a_2_5_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_26]),c_0_27]),c_0_19])]),c_0_17])).

cnf(c_0_71,negated_conjecture,
    ( r1_lattices(esk8_0,k15_lattice3(esk8_0,X1),k15_lattice3(esk8_0,X2))
    | ~ r2_hidden(k15_lattice3(esk8_0,X2),a_2_4_lattice3(esk8_0,k15_lattice3(esk8_0,X1))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_23])).

cnf(c_0_72,negated_conjecture,
    ( k15_lattice3(esk8_0,a_2_3_lattice3(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0))) = esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_38]),c_0_26]),c_0_27]),c_0_19])]),c_0_17])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,a_2_4_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattices(X2,X3,X1)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( r3_lattices(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),k15_lattice3(esk8_0,esk10_0))
    | r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( r1_lattices(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),k15_lattice3(esk8_0,X1))
    | ~ r2_hidden(k15_lattice3(esk8_0,X1),a_2_4_lattice3(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_4_lattice3(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)))
    | r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_26]),c_0_27]),c_0_38]),c_0_23]),c_0_19])]),c_0_17])).

cnf(c_0_77,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk2_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_78,negated_conjecture,
    ( r1_lattices(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),k15_lattice3(esk8_0,esk10_0))
    | r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( r4_lattice3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)
    | r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_23]),c_0_19])]),c_0_17])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_79]),c_0_26]),c_0_27]),c_0_23]),c_0_19])]),c_0_17])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_80]),c_0_33]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.19/0.47  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.030 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t48_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattice3)).
% 0.19/0.47  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.19/0.47  fof(fraenkel_a_2_2_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_2_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r4_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 0.19/0.47  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 0.19/0.47  fof(t38_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 0.19/0.47  fof(t37_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 0.19/0.47  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 0.19/0.47  fof(t45_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k15_lattice3(X1,a_2_3_lattice3(X1,X2))&X2=k16_lattice3(X1,a_2_4_lattice3(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_lattice3)).
% 0.19/0.47  fof(fraenkel_a_2_5_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_5_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r3_lattices(X2,X4,X5))&r2_hidden(X5,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_5_lattice3)).
% 0.19/0.47  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 0.19/0.47  fof(t47_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(k15_lattice3(X1,X2)=k15_lattice3(X1,a_2_5_lattice3(X1,X2))&k16_lattice3(X1,X2)=k16_lattice3(X1,a_2_6_lattice3(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_lattice3)).
% 0.19/0.47  fof(fraenkel_a_2_4_lattice3, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))&m1_subset_1(X3,u1_struct_0(X2)))=>(r2_hidden(X1,a_2_4_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r3_lattices(X2,X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_4_lattice3)).
% 0.19/0.47  fof(c_0_12, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))))), inference(assume_negation,[status(cth)],[t48_lattice3])).
% 0.19/0.47  fof(c_0_13, negated_conjecture, ![X57]:((((~v2_struct_0(esk8_0)&v10_lattices(esk8_0))&v4_lattice3(esk8_0))&l3_lattices(esk8_0))&(((m1_subset_1(esk11_1(X57),u1_struct_0(esk8_0))|~r2_hidden(X57,esk9_0)|~m1_subset_1(X57,u1_struct_0(esk8_0)))&((r3_lattices(esk8_0,X57,esk11_1(X57))|~r2_hidden(X57,esk9_0)|~m1_subset_1(X57,u1_struct_0(esk8_0)))&(r2_hidden(esk11_1(X57),esk10_0)|~r2_hidden(X57,esk9_0)|~m1_subset_1(X57,u1_struct_0(esk8_0)))))&~r3_lattices(esk8_0,k15_lattice3(esk8_0,esk9_0),k15_lattice3(esk8_0,esk10_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).
% 0.19/0.47  fof(c_0_14, plain, ![X18, X19]:(v2_struct_0(X18)|~l3_lattices(X18)|m1_subset_1(k15_lattice3(X18,X19),u1_struct_0(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.19/0.47  fof(c_0_15, plain, ![X20, X21, X22, X24, X25]:((((m1_subset_1(esk3_3(X20,X21,X22),u1_struct_0(X21))|~r2_hidden(X20,a_2_2_lattice3(X21,X22))|(v2_struct_0(X21)|~v10_lattices(X21)|~v4_lattice3(X21)|~l3_lattices(X21)))&(X20=esk3_3(X20,X21,X22)|~r2_hidden(X20,a_2_2_lattice3(X21,X22))|(v2_struct_0(X21)|~v10_lattices(X21)|~v4_lattice3(X21)|~l3_lattices(X21))))&(r4_lattice3(X21,esk3_3(X20,X21,X22),X22)|~r2_hidden(X20,a_2_2_lattice3(X21,X22))|(v2_struct_0(X21)|~v10_lattices(X21)|~v4_lattice3(X21)|~l3_lattices(X21))))&(~m1_subset_1(X25,u1_struct_0(X21))|X20!=X25|~r4_lattice3(X21,X25,X24)|r2_hidden(X20,a_2_2_lattice3(X21,X24))|(v2_struct_0(X21)|~v10_lattices(X21)|~v4_lattice3(X21)|~l3_lattices(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).
% 0.19/0.47  fof(c_0_16, plain, ![X12, X13, X14, X15, X16]:((~r4_lattice3(X12,X13,X14)|(~m1_subset_1(X15,u1_struct_0(X12))|(~r2_hidden(X15,X14)|r1_lattices(X12,X15,X13)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~l3_lattices(X12)))&((m1_subset_1(esk2_3(X12,X13,X16),u1_struct_0(X12))|r4_lattice3(X12,X13,X16)|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~l3_lattices(X12)))&((r2_hidden(esk2_3(X12,X13,X16),X16)|r4_lattice3(X12,X13,X16)|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~l3_lattices(X12)))&(~r1_lattices(X12,esk2_3(X12,X13,X16),X13)|r4_lattice3(X12,X13,X16)|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~l3_lattices(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.19/0.47  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.47  cnf(c_0_18, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  cnf(c_0_19, negated_conjecture, (l3_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.47  fof(c_0_20, plain, ![X47, X48, X49]:((r3_lattices(X47,X48,k15_lattice3(X47,X49))|~r2_hidden(X48,X49)|~m1_subset_1(X48,u1_struct_0(X47))|(v2_struct_0(X47)|~v10_lattices(X47)|~v4_lattice3(X47)|~l3_lattices(X47)))&(r3_lattices(X47,k16_lattice3(X47,X49),X48)|~r2_hidden(X48,X49)|~m1_subset_1(X48,u1_struct_0(X47))|(v2_struct_0(X47)|~v10_lattices(X47)|~v4_lattice3(X47)|~l3_lattices(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).
% 0.19/0.47  cnf(c_0_21, plain, (r2_hidden(X3,a_2_2_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r4_lattice3(X2,X1,X4)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.47  cnf(c_0_22, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.47  cnf(c_0_23, negated_conjecture, (m1_subset_1(k15_lattice3(esk8_0,X1),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.19/0.47  fof(c_0_24, plain, ![X45, X46]:(v2_struct_0(X45)|~v10_lattices(X45)|~v4_lattice3(X45)|~l3_lattices(X45)|k15_lattice3(X45,X46)=k16_lattice3(X45,a_2_2_lattice3(X45,X46))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).
% 0.19/0.47  cnf(c_0_25, plain, (r3_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  cnf(c_0_26, negated_conjecture, (v4_lattice3(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.47  cnf(c_0_27, negated_conjecture, (v10_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.47  cnf(c_0_28, plain, (r2_hidden(X1,a_2_2_lattice3(X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.47  cnf(c_0_29, negated_conjecture, (r4_lattice3(esk8_0,k15_lattice3(esk8_0,X1),X2)|m1_subset_1(esk2_3(esk8_0,k15_lattice3(esk8_0,X1),X2),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_19])]), c_0_17])).
% 0.19/0.47  cnf(c_0_30, plain, (v2_struct_0(X1)|k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.47  cnf(c_0_31, negated_conjecture, (r3_lattices(esk8_0,k16_lattice3(esk8_0,X1),k15_lattice3(esk8_0,X2))|~r2_hidden(k15_lattice3(esk8_0,X2),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_23]), c_0_26]), c_0_27]), c_0_19])]), c_0_17])).
% 0.19/0.47  cnf(c_0_32, negated_conjecture, (r2_hidden(k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2))|m1_subset_1(esk2_3(esk8_0,k15_lattice3(esk8_0,X1),X2),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_26]), c_0_27]), c_0_23]), c_0_19])]), c_0_17])).
% 0.19/0.47  cnf(c_0_33, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_26]), c_0_27]), c_0_19])]), c_0_17])).
% 0.19/0.47  cnf(c_0_34, negated_conjecture, (~r3_lattices(esk8_0,k15_lattice3(esk8_0,esk9_0),k15_lattice3(esk8_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.47  cnf(c_0_35, negated_conjecture, (r3_lattices(esk8_0,k15_lattice3(esk8_0,X1),k15_lattice3(esk8_0,X2))|m1_subset_1(esk2_3(esk8_0,k15_lattice3(esk8_0,X2),X1),u1_struct_0(esk8_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.19/0.47  cnf(c_0_36, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.47  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk11_1(X1),u1_struct_0(esk8_0))|~r2_hidden(X1,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.47  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.47  cnf(c_0_39, negated_conjecture, (r4_lattice3(esk8_0,k15_lattice3(esk8_0,X1),X2)|r2_hidden(esk2_3(esk8_0,k15_lattice3(esk8_0,X1),X2),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_23]), c_0_19])]), c_0_17])).
% 0.19/0.47  fof(c_0_40, plain, ![X39, X40, X41, X42, X43]:(((r3_lattice3(X39,X40,X41)|X40!=k16_lattice3(X39,X41)|~m1_subset_1(X40,u1_struct_0(X39))|(v2_struct_0(X39)|~v10_lattices(X39)|~v4_lattice3(X39)|~l3_lattices(X39)))&(~m1_subset_1(X42,u1_struct_0(X39))|(~r3_lattice3(X39,X42,X41)|r3_lattices(X39,X42,X40))|X40!=k16_lattice3(X39,X41)|~m1_subset_1(X40,u1_struct_0(X39))|(v2_struct_0(X39)|~v10_lattices(X39)|~v4_lattice3(X39)|~l3_lattices(X39))))&((m1_subset_1(esk7_3(X39,X40,X43),u1_struct_0(X39))|~r3_lattice3(X39,X40,X43)|X40=k16_lattice3(X39,X43)|~m1_subset_1(X40,u1_struct_0(X39))|(v2_struct_0(X39)|~v10_lattices(X39)|~v4_lattice3(X39)|~l3_lattices(X39)))&((r3_lattice3(X39,esk7_3(X39,X40,X43),X43)|~r3_lattice3(X39,X40,X43)|X40=k16_lattice3(X39,X43)|~m1_subset_1(X40,u1_struct_0(X39))|(v2_struct_0(X39)|~v10_lattices(X39)|~v4_lattice3(X39)|~l3_lattices(X39)))&(~r3_lattices(X39,esk7_3(X39,X40,X43),X40)|~r3_lattice3(X39,X40,X43)|X40=k16_lattice3(X39,X43)|~m1_subset_1(X40,u1_struct_0(X39))|(v2_struct_0(X39)|~v10_lattices(X39)|~v4_lattice3(X39)|~l3_lattices(X39)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.19/0.47  fof(c_0_41, plain, ![X50, X51]:((X51=k15_lattice3(X50,a_2_3_lattice3(X50,X51))|~m1_subset_1(X51,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50)))&(X51=k16_lattice3(X50,a_2_4_lattice3(X50,X51))|~m1_subset_1(X51,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).
% 0.19/0.47  fof(c_0_42, plain, ![X31, X32, X33, X36, X37, X38]:((((m1_subset_1(esk5_3(X31,X32,X33),u1_struct_0(X32))|~r2_hidden(X31,a_2_5_lattice3(X32,X33))|(v2_struct_0(X32)|~v10_lattices(X32)|~v4_lattice3(X32)|~l3_lattices(X32)))&(X31=esk5_3(X31,X32,X33)|~r2_hidden(X31,a_2_5_lattice3(X32,X33))|(v2_struct_0(X32)|~v10_lattices(X32)|~v4_lattice3(X32)|~l3_lattices(X32))))&(((m1_subset_1(esk6_3(X31,X32,X33),u1_struct_0(X32))|~r2_hidden(X31,a_2_5_lattice3(X32,X33))|(v2_struct_0(X32)|~v10_lattices(X32)|~v4_lattice3(X32)|~l3_lattices(X32)))&(r3_lattices(X32,esk5_3(X31,X32,X33),esk6_3(X31,X32,X33))|~r2_hidden(X31,a_2_5_lattice3(X32,X33))|(v2_struct_0(X32)|~v10_lattices(X32)|~v4_lattice3(X32)|~l3_lattices(X32))))&(r2_hidden(esk6_3(X31,X32,X33),X33)|~r2_hidden(X31,a_2_5_lattice3(X32,X33))|(v2_struct_0(X32)|~v10_lattices(X32)|~v4_lattice3(X32)|~l3_lattices(X32)))))&(~m1_subset_1(X37,u1_struct_0(X32))|X31!=X37|(~m1_subset_1(X38,u1_struct_0(X32))|~r3_lattices(X32,X37,X38)|~r2_hidden(X38,X36))|r2_hidden(X31,a_2_5_lattice3(X32,X36))|(v2_struct_0(X32)|~v10_lattices(X32)|~v4_lattice3(X32)|~l3_lattices(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_5_lattice3])])])])])])])).
% 0.19/0.47  cnf(c_0_43, negated_conjecture, (r3_lattices(esk8_0,X1,esk11_1(X1))|~r2_hidden(X1,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.47  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk11_1(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)),u1_struct_0(esk8_0))|~r2_hidden(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),esk9_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.47  cnf(c_0_45, negated_conjecture, (r2_hidden(esk2_3(esk8_0,k15_lattice3(esk8_0,X1),X2),X2)|r2_hidden(k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_39]), c_0_26]), c_0_27]), c_0_23]), c_0_19])]), c_0_17])).
% 0.19/0.47  cnf(c_0_46, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|X2!=k16_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.47  cnf(c_0_47, plain, (X1=k16_lattice3(X2,a_2_4_lattice3(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.47  cnf(c_0_48, plain, (r2_hidden(X3,a_2_5_lattice3(X2,X5))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~m1_subset_1(X4,u1_struct_0(X2))|~r3_lattices(X2,X1,X4)|~r2_hidden(X4,X5)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.47  cnf(c_0_49, negated_conjecture, (r3_lattices(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),esk11_1(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)))|~r2_hidden(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),esk9_0)), inference(spm,[status(thm)],[c_0_43, c_0_38])).
% 0.19/0.47  cnf(c_0_50, negated_conjecture, (r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0))|m1_subset_1(esk11_1(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.47  fof(c_0_51, plain, ![X6, X7, X8, X9, X10]:((~r3_lattice3(X6,X7,X8)|(~m1_subset_1(X9,u1_struct_0(X6))|(~r2_hidden(X9,X8)|r1_lattices(X6,X7,X9)))|~m1_subset_1(X7,u1_struct_0(X6))|(v2_struct_0(X6)|~l3_lattices(X6)))&((m1_subset_1(esk1_3(X6,X7,X10),u1_struct_0(X6))|r3_lattice3(X6,X7,X10)|~m1_subset_1(X7,u1_struct_0(X6))|(v2_struct_0(X6)|~l3_lattices(X6)))&((r2_hidden(esk1_3(X6,X7,X10),X10)|r3_lattice3(X6,X7,X10)|~m1_subset_1(X7,u1_struct_0(X6))|(v2_struct_0(X6)|~l3_lattices(X6)))&(~r1_lattices(X6,X7,esk1_3(X6,X7,X10))|r3_lattice3(X6,X7,X10)|~m1_subset_1(X7,u1_struct_0(X6))|(v2_struct_0(X6)|~l3_lattices(X6)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.19/0.47  cnf(c_0_52, plain, (r3_lattice3(X1,k16_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_46])).
% 0.19/0.47  cnf(c_0_53, negated_conjecture, (k16_lattice3(esk8_0,a_2_4_lattice3(esk8_0,k15_lattice3(esk8_0,X1)))=k15_lattice3(esk8_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_23]), c_0_26]), c_0_27]), c_0_19])]), c_0_17])).
% 0.19/0.47  cnf(c_0_54, plain, (r2_hidden(X1,a_2_5_lattice3(X2,X3))|v2_struct_0(X2)|~r3_lattices(X2,X1,X4)|~v4_lattice3(X2)|~v10_lattices(X2)|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_48])).
% 0.19/0.47  cnf(c_0_55, negated_conjecture, (r3_lattices(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),esk11_1(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)))|r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_49, c_0_45])).
% 0.19/0.47  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk11_1(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_50]), c_0_33]), c_0_34])).
% 0.19/0.47  fof(c_0_57, plain, ![X52, X53]:((k15_lattice3(X52,X53)=k15_lattice3(X52,a_2_5_lattice3(X52,X53))|(v2_struct_0(X52)|~v10_lattices(X52)|~v4_lattice3(X52)|~l3_lattices(X52)))&(k16_lattice3(X52,X53)=k16_lattice3(X52,a_2_6_lattice3(X52,X53))|(v2_struct_0(X52)|~v10_lattices(X52)|~v4_lattice3(X52)|~l3_lattices(X52)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).
% 0.19/0.47  cnf(c_0_58, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.47  cnf(c_0_59, negated_conjecture, (r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),a_2_4_lattice3(esk8_0,k15_lattice3(esk8_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_26]), c_0_27]), c_0_23]), c_0_19])]), c_0_17])).
% 0.19/0.47  fof(c_0_60, plain, ![X26, X27, X28, X30]:((((m1_subset_1(esk4_3(X26,X27,X28),u1_struct_0(X27))|~r2_hidden(X26,a_2_4_lattice3(X27,X28))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27)|~m1_subset_1(X28,u1_struct_0(X27))))&(X26=esk4_3(X26,X27,X28)|~r2_hidden(X26,a_2_4_lattice3(X27,X28))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27)|~m1_subset_1(X28,u1_struct_0(X27)))))&(r3_lattices(X27,X28,esk4_3(X26,X27,X28))|~r2_hidden(X26,a_2_4_lattice3(X27,X28))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27)|~m1_subset_1(X28,u1_struct_0(X27)))))&(~m1_subset_1(X30,u1_struct_0(X27))|X26!=X30|~r3_lattices(X27,X28,X30)|r2_hidden(X26,a_2_4_lattice3(X27,X28))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27)|~m1_subset_1(X28,u1_struct_0(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_4_lattice3])])])])])])).
% 0.19/0.47  cnf(c_0_61, plain, (r3_lattices(X1,X2,k15_lattice3(X1,X3))|v2_struct_0(X1)|~r2_hidden(X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  cnf(c_0_62, negated_conjecture, (r2_hidden(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),a_2_5_lattice3(esk8_0,X1))|r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0))|~r2_hidden(esk11_1(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_26]), c_0_27]), c_0_56]), c_0_38]), c_0_19])]), c_0_17])).
% 0.19/0.47  cnf(c_0_63, negated_conjecture, (r2_hidden(esk11_1(X1),esk10_0)|~r2_hidden(X1,esk9_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.47  cnf(c_0_64, plain, (k15_lattice3(X1,X2)=k15_lattice3(X1,a_2_5_lattice3(X1,X2))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.47  cnf(c_0_65, negated_conjecture, (r1_lattices(esk8_0,k15_lattice3(esk8_0,X1),X2)|~r2_hidden(X2,a_2_4_lattice3(esk8_0,k15_lattice3(esk8_0,X1)))|~m1_subset_1(X2,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_23]), c_0_19])]), c_0_17])).
% 0.19/0.47  cnf(c_0_66, plain, (X1=k15_lattice3(X2,a_2_3_lattice3(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.47  cnf(c_0_67, plain, (r2_hidden(X3,a_2_4_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r3_lattices(X2,X4,X1)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~m1_subset_1(X4,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.47  cnf(c_0_68, negated_conjecture, (r3_lattices(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),k15_lattice3(esk8_0,X1))|~r2_hidden(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_38]), c_0_26]), c_0_27]), c_0_19])]), c_0_17])).
% 0.19/0.47  cnf(c_0_69, negated_conjecture, (r2_hidden(esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),a_2_5_lattice3(esk8_0,esk10_0))|r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_38])]), c_0_45])).
% 0.19/0.47  cnf(c_0_70, negated_conjecture, (k15_lattice3(esk8_0,a_2_5_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_26]), c_0_27]), c_0_19])]), c_0_17])).
% 0.19/0.47  cnf(c_0_71, negated_conjecture, (r1_lattices(esk8_0,k15_lattice3(esk8_0,X1),k15_lattice3(esk8_0,X2))|~r2_hidden(k15_lattice3(esk8_0,X2),a_2_4_lattice3(esk8_0,k15_lattice3(esk8_0,X1)))), inference(spm,[status(thm)],[c_0_65, c_0_23])).
% 0.19/0.47  cnf(c_0_72, negated_conjecture, (k15_lattice3(esk8_0,a_2_3_lattice3(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)))=esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_38]), c_0_26]), c_0_27]), c_0_19])]), c_0_17])).
% 0.19/0.47  cnf(c_0_73, plain, (r2_hidden(X1,a_2_4_lattice3(X2,X3))|v2_struct_0(X2)|~r3_lattices(X2,X3,X1)|~v4_lattice3(X2)|~v10_lattices(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_67])).
% 0.19/0.47  cnf(c_0_74, negated_conjecture, (r3_lattices(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),k15_lattice3(esk8_0,esk10_0))|r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.19/0.47  cnf(c_0_75, negated_conjecture, (r1_lattices(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),k15_lattice3(esk8_0,X1))|~r2_hidden(k15_lattice3(esk8_0,X1),a_2_4_lattice3(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.19/0.47  cnf(c_0_76, negated_conjecture, (r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_4_lattice3(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)))|r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_26]), c_0_27]), c_0_38]), c_0_23]), c_0_19])]), c_0_17])).
% 0.19/0.47  cnf(c_0_77, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk2_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.47  cnf(c_0_78, negated_conjecture, (r1_lattices(esk8_0,esk2_3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0),k15_lattice3(esk8_0,esk10_0))|r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.47  cnf(c_0_79, negated_conjecture, (r4_lattice3(esk8_0,k15_lattice3(esk8_0,esk10_0),esk9_0)|r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_23]), c_0_19])]), c_0_17])).
% 0.19/0.47  cnf(c_0_80, negated_conjecture, (r2_hidden(k15_lattice3(esk8_0,esk10_0),a_2_2_lattice3(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_79]), c_0_26]), c_0_27]), c_0_23]), c_0_19])]), c_0_17])).
% 0.19/0.47  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_80]), c_0_33]), c_0_34]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 82
% 0.19/0.47  # Proof object clause steps            : 57
% 0.19/0.47  # Proof object formula steps           : 25
% 0.19/0.47  # Proof object conjectures             : 41
% 0.19/0.47  # Proof object clause conjectures      : 38
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 23
% 0.19/0.47  # Proof object initial formulas used   : 12
% 0.19/0.47  # Proof object generating inferences   : 30
% 0.19/0.47  # Proof object simplifying inferences  : 95
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 12
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 43
% 0.19/0.47  # Removed in clause preprocessing      : 0
% 0.19/0.47  # Initial clauses in saturation        : 43
% 0.19/0.47  # Processed clauses                    : 718
% 0.19/0.47  # ...of these trivial                  : 31
% 0.19/0.47  # ...subsumed                          : 233
% 0.19/0.47  # ...remaining for further processing  : 454
% 0.19/0.47  # Other redundant clauses eliminated   : 5
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 3
% 0.19/0.47  # Backward-rewritten                   : 73
% 0.19/0.47  # Generated clauses                    : 4563
% 0.19/0.47  # ...of the previous two non-trivial   : 4239
% 0.19/0.47  # Contextual simplify-reflections      : 5
% 0.19/0.47  # Paramodulations                      : 4558
% 0.19/0.47  # Factorizations                       : 0
% 0.19/0.47  # Equation resolutions                 : 5
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 330
% 0.19/0.47  #    Positive orientable unit clauses  : 101
% 0.19/0.47  #    Positive unorientable unit clauses: 0
% 0.19/0.47  #    Negative unit clauses             : 2
% 0.19/0.47  #    Non-unit-clauses                  : 227
% 0.19/0.47  # Current number of unprocessed clauses: 3471
% 0.19/0.47  # ...number of literals in the above   : 8553
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 119
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 5859
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 4545
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 238
% 0.19/0.47  # Unit Clause-clause subsumption calls : 599
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 406
% 0.19/0.47  # BW rewrite match successes           : 32
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 131492
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.120 s
% 0.19/0.47  # System time              : 0.007 s
% 0.19/0.47  # Total time               : 0.127 s
% 0.19/0.47  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
