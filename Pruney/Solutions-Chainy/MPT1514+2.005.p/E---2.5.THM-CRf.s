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

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 (1508 expanded)
%              Number of clauses        :   46 ( 486 expanded)
%              Number of leaves         :    9 ( 370 expanded)
%              Depth                    :   18
%              Number of atoms          :  419 (12056 expanded)
%              Number of equality atoms :   26 ( 232 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
    ! [X38,X39] :
      ( ( k15_lattice3(X38,X39) = k15_lattice3(X38,a_2_5_lattice3(X38,X39))
        | v2_struct_0(X38)
        | ~ v10_lattices(X38)
        | ~ v4_lattice3(X38)
        | ~ l3_lattices(X38) )
      & ( k16_lattice3(X38,X39) = k16_lattice3(X38,a_2_6_lattice3(X38,X39))
        | v2_struct_0(X38)
        | ~ v10_lattices(X38)
        | ~ v4_lattice3(X38)
        | ~ l3_lattices(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).

fof(c_0_11,negated_conjecture,(
    ! [X43] :
      ( ~ v2_struct_0(esk6_0)
      & v10_lattices(esk6_0)
      & v4_lattice3(esk6_0)
      & l3_lattices(esk6_0)
      & ( m1_subset_1(esk9_1(X43),u1_struct_0(esk6_0))
        | ~ r2_hidden(X43,esk7_0)
        | ~ m1_subset_1(X43,u1_struct_0(esk6_0)) )
      & ( r3_lattices(esk6_0,X43,esk9_1(X43))
        | ~ r2_hidden(X43,esk7_0)
        | ~ m1_subset_1(X43,u1_struct_0(esk6_0)) )
      & ( r2_hidden(esk9_1(X43),esk8_0)
        | ~ r2_hidden(X43,esk7_0)
        | ~ m1_subset_1(X43,u1_struct_0(esk6_0)) )
      & ~ r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0)) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).

fof(c_0_12,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ l3_lattices(X17)
      | m1_subset_1(k15_lattice3(X17,X18),u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

cnf(c_0_13,plain,
    ( k15_lattice3(X1,X2) = k15_lattice3(X1,a_2_5_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v4_lattice3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v10_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( l3_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X19,X20,X21,X23,X24] :
      ( ( m1_subset_1(esk3_3(X19,X20,X21),u1_struct_0(X20))
        | ~ r2_hidden(X19,a_2_2_lattice3(X20,X21))
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ v4_lattice3(X20)
        | ~ l3_lattices(X20) )
      & ( X19 = esk3_3(X19,X20,X21)
        | ~ r2_hidden(X19,a_2_2_lattice3(X20,X21))
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ v4_lattice3(X20)
        | ~ l3_lattices(X20) )
      & ( r4_lattice3(X20,esk3_3(X19,X20,X21),X21)
        | ~ r2_hidden(X19,a_2_2_lattice3(X20,X21))
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ v4_lattice3(X20)
        | ~ l3_lattices(X20) )
      & ( ~ m1_subset_1(X24,u1_struct_0(X20))
        | X19 != X24
        | ~ r4_lattice3(X20,X24,X23)
        | r2_hidden(X19,a_2_2_lattice3(X20,X23))
        | v2_struct_0(X20)
        | ~ v10_lattices(X20)
        | ~ v4_lattice3(X20)
        | ~ l3_lattices(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).

fof(c_0_19,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r4_lattice3(X6,X7,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | ~ r2_hidden(X9,X8)
        | r1_lattices(X6,X9,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) )
      & ( m1_subset_1(esk1_3(X6,X7,X10),u1_struct_0(X6))
        | r4_lattice3(X6,X7,X10)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) )
      & ( r2_hidden(esk1_3(X6,X7,X10),X10)
        | r4_lattice3(X6,X7,X10)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) )
      & ( ~ r1_lattices(X6,esk1_3(X6,X7,X10),X7)
        | r4_lattice3(X6,X7,X10)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( k15_lattice3(esk6_0,a_2_5_lattice3(esk6_0,X1)) = k15_lattice3(esk6_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

fof(c_0_22,plain,(
    ! [X35,X36,X37] :
      ( ( r3_lattices(X35,X36,k15_lattice3(X35,X37))
        | ~ r2_hidden(X36,X37)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) )
      & ( r3_lattices(X35,k16_lattice3(X35,X37),X36)
        | ~ r2_hidden(X36,X37)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X3,a_2_2_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r4_lattice3(X2,X1,X4)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk6_0,X1),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_16])]),c_0_17])).

fof(c_0_26,plain,(
    ! [X33,X34] :
      ( v2_struct_0(X33)
      | ~ v10_lattices(X33)
      | ~ v4_lattice3(X33)
      | ~ l3_lattices(X33)
      | k15_lattice3(X33,X34) = k16_lattice3(X33,a_2_2_lattice3(X33,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).

cnf(c_0_27,plain,
    ( r3_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r4_lattice3(esk6_0,k15_lattice3(esk6_0,X1),X2)
    | m1_subset_1(esk1_3(esk6_0,k15_lattice3(esk6_0,X1),X2),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_16])]),c_0_17])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r3_lattices(esk6_0,k16_lattice3(esk6_0,X1),k15_lattice3(esk6_0,X2))
    | ~ r2_hidden(k15_lattice3(esk6_0,X2),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk6_0,X1),a_2_2_lattice3(esk6_0,X2))
    | m1_subset_1(esk1_3(esk6_0,k15_lattice3(esk6_0,X1),X2),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_14]),c_0_15]),c_0_25]),c_0_16])]),c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,X1)) = k15_lattice3(esk6_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( ~ r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( r3_lattices(esk6_0,k15_lattice3(esk6_0,X1),k15_lattice3(esk6_0,X2))
    | m1_subset_1(esk1_3(esk6_0,k15_lattice3(esk6_0,X2),X1),u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_37,plain,(
    ! [X12,X13,X14,X15] :
      ( ( r4_lattice3(X12,X14,X13)
        | X14 != k15_lattice3(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ v4_lattice3(X12)
        | ~ l3_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r4_lattice3(X12,X15,X13)
        | r1_lattices(X12,X14,X15)
        | X14 != k15_lattice3(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ v4_lattice3(X12)
        | ~ l3_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk2_3(X12,X13,X14),u1_struct_0(X12))
        | ~ r4_lattice3(X12,X14,X13)
        | X14 = k15_lattice3(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ v4_lattice3(X12)
        | ~ l3_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( r4_lattice3(X12,esk2_3(X12,X13,X14),X13)
        | ~ r4_lattice3(X12,X14,X13)
        | X14 = k15_lattice3(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ v4_lattice3(X12)
        | ~ l3_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( ~ r1_lattices(X12,X14,esk2_3(X12,X13,X14))
        | ~ r4_lattice3(X12,X14,X13)
        | X14 = k15_lattice3(X12,X13)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ v4_lattice3(X12)
        | ~ l3_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk9_1(X1),u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_3(esk6_0,k15_lattice3(esk6_0,X1),X2),X2)
    | r4_lattice3(esk6_0,k15_lattice3(esk6_0,X1),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_25]),c_0_16])]),c_0_17])).

cnf(c_0_41,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_42,plain,(
    ! [X25,X26,X27,X30,X31,X32] :
      ( ( m1_subset_1(esk4_3(X25,X26,X27),u1_struct_0(X26))
        | ~ r2_hidden(X25,a_2_5_lattice3(X26,X27))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26) )
      & ( X25 = esk4_3(X25,X26,X27)
        | ~ r2_hidden(X25,a_2_5_lattice3(X26,X27))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26) )
      & ( m1_subset_1(esk5_3(X25,X26,X27),u1_struct_0(X26))
        | ~ r2_hidden(X25,a_2_5_lattice3(X26,X27))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26) )
      & ( r3_lattices(X26,esk4_3(X25,X26,X27),esk5_3(X25,X26,X27))
        | ~ r2_hidden(X25,a_2_5_lattice3(X26,X27))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26) )
      & ( r2_hidden(esk5_3(X25,X26,X27),X27)
        | ~ r2_hidden(X25,a_2_5_lattice3(X26,X27))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26) )
      & ( ~ m1_subset_1(X31,u1_struct_0(X26))
        | X25 != X31
        | ~ m1_subset_1(X32,u1_struct_0(X26))
        | ~ r3_lattices(X26,X31,X32)
        | ~ r2_hidden(X32,X30)
        | r2_hidden(X25,a_2_5_lattice3(X26,X30))
        | v2_struct_0(X26)
        | ~ v10_lattices(X26)
        | ~ v4_lattice3(X26)
        | ~ l3_lattices(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_5_lattice3])])])])])])])).

cnf(c_0_43,negated_conjecture,
    ( r3_lattices(esk6_0,X1,esk9_1(X1))
    | ~ r2_hidden(X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk9_1(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0)),u1_struct_0(esk6_0))
    | ~ r2_hidden(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_3(esk6_0,k15_lattice3(esk6_0,X1),X2),X2)
    | r2_hidden(k15_lattice3(esk6_0,X1),a_2_2_lattice3(esk6_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_40]),c_0_14]),c_0_15]),c_0_25]),c_0_16])]),c_0_17])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | r4_lattice3(X1,X2,X3)
    | X2 != k15_lattice3(X1,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
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

cnf(c_0_48,negated_conjecture,
    ( r3_lattices(esk6_0,esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),esk9_1(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0)))
    | ~ r2_hidden(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk6_0,esk8_0),a_2_2_lattice3(esk6_0,esk7_0))
    | m1_subset_1(esk9_1(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0)),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_51,plain,
    ( r4_lattice3(X1,k15_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_46]),c_0_20])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,a_2_5_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattices(X2,X1,X4)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r3_lattices(esk6_0,esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),esk9_1(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0)))
    | r2_hidden(k15_lattice3(esk6_0,esk8_0),a_2_2_lattice3(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk9_1(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0)),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_49]),c_0_33]),c_0_34])).

cnf(c_0_55,plain,
    ( r1_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_20])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),a_2_5_lattice3(esk6_0,X1))
    | r2_hidden(k15_lattice3(esk6_0,esk8_0),a_2_2_lattice3(esk6_0,esk7_0))
    | ~ r2_hidden(esk9_1(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0)),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_14]),c_0_15]),c_0_54]),c_0_39]),c_0_16])]),c_0_17])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk9_1(X1),esk8_0)
    | ~ r2_hidden(X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_58,negated_conjecture,
    ( r1_lattices(esk6_0,esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),k15_lattice3(esk6_0,X1))
    | ~ r2_hidden(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_39]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),a_2_5_lattice3(esk6_0,esk8_0))
    | r2_hidden(k15_lattice3(esk6_0,esk8_0),a_2_2_lattice3(esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_39])]),c_0_45])).

cnf(c_0_60,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk1_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_61,negated_conjecture,
    ( r1_lattices(esk6_0,esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),k15_lattice3(esk6_0,esk8_0))
    | r2_hidden(k15_lattice3(esk6_0,esk8_0),a_2_2_lattice3(esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_21])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk6_0,esk8_0),a_2_2_lattice3(esk6_0,esk7_0))
    | r4_lattice3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_25]),c_0_16])]),c_0_17])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk6_0,esk8_0),a_2_2_lattice3(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_62]),c_0_14]),c_0_15]),c_0_25]),c_0_16])]),c_0_17])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_63]),c_0_33]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:50:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.20/0.40  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.029 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t48_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattice3)).
% 0.20/0.40  fof(t47_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(k15_lattice3(X1,X2)=k15_lattice3(X1,a_2_5_lattice3(X1,X2))&k16_lattice3(X1,X2)=k16_lattice3(X1,a_2_6_lattice3(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_lattice3)).
% 0.20/0.40  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.20/0.40  fof(fraenkel_a_2_2_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_2_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r4_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 0.20/0.40  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 0.20/0.40  fof(t38_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 0.20/0.40  fof(t37_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 0.20/0.40  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 0.20/0.40  fof(fraenkel_a_2_5_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_5_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r3_lattices(X2,X4,X5))&r2_hidden(X5,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_5_lattice3)).
% 0.20/0.40  fof(c_0_9, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))))), inference(assume_negation,[status(cth)],[t48_lattice3])).
% 0.20/0.40  fof(c_0_10, plain, ![X38, X39]:((k15_lattice3(X38,X39)=k15_lattice3(X38,a_2_5_lattice3(X38,X39))|(v2_struct_0(X38)|~v10_lattices(X38)|~v4_lattice3(X38)|~l3_lattices(X38)))&(k16_lattice3(X38,X39)=k16_lattice3(X38,a_2_6_lattice3(X38,X39))|(v2_struct_0(X38)|~v10_lattices(X38)|~v4_lattice3(X38)|~l3_lattices(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_lattice3])])])])])).
% 0.20/0.40  fof(c_0_11, negated_conjecture, ![X43]:((((~v2_struct_0(esk6_0)&v10_lattices(esk6_0))&v4_lattice3(esk6_0))&l3_lattices(esk6_0))&(((m1_subset_1(esk9_1(X43),u1_struct_0(esk6_0))|~r2_hidden(X43,esk7_0)|~m1_subset_1(X43,u1_struct_0(esk6_0)))&((r3_lattices(esk6_0,X43,esk9_1(X43))|~r2_hidden(X43,esk7_0)|~m1_subset_1(X43,u1_struct_0(esk6_0)))&(r2_hidden(esk9_1(X43),esk8_0)|~r2_hidden(X43,esk7_0)|~m1_subset_1(X43,u1_struct_0(esk6_0)))))&~r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).
% 0.20/0.40  fof(c_0_12, plain, ![X17, X18]:(v2_struct_0(X17)|~l3_lattices(X17)|m1_subset_1(k15_lattice3(X17,X18),u1_struct_0(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.20/0.40  cnf(c_0_13, plain, (k15_lattice3(X1,X2)=k15_lattice3(X1,a_2_5_lattice3(X1,X2))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_14, negated_conjecture, (v4_lattice3(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_15, negated_conjecture, (v10_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_16, negated_conjecture, (l3_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  fof(c_0_18, plain, ![X19, X20, X21, X23, X24]:((((m1_subset_1(esk3_3(X19,X20,X21),u1_struct_0(X20))|~r2_hidden(X19,a_2_2_lattice3(X20,X21))|(v2_struct_0(X20)|~v10_lattices(X20)|~v4_lattice3(X20)|~l3_lattices(X20)))&(X19=esk3_3(X19,X20,X21)|~r2_hidden(X19,a_2_2_lattice3(X20,X21))|(v2_struct_0(X20)|~v10_lattices(X20)|~v4_lattice3(X20)|~l3_lattices(X20))))&(r4_lattice3(X20,esk3_3(X19,X20,X21),X21)|~r2_hidden(X19,a_2_2_lattice3(X20,X21))|(v2_struct_0(X20)|~v10_lattices(X20)|~v4_lattice3(X20)|~l3_lattices(X20))))&(~m1_subset_1(X24,u1_struct_0(X20))|X19!=X24|~r4_lattice3(X20,X24,X23)|r2_hidden(X19,a_2_2_lattice3(X20,X23))|(v2_struct_0(X20)|~v10_lattices(X20)|~v4_lattice3(X20)|~l3_lattices(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).
% 0.20/0.40  fof(c_0_19, plain, ![X6, X7, X8, X9, X10]:((~r4_lattice3(X6,X7,X8)|(~m1_subset_1(X9,u1_struct_0(X6))|(~r2_hidden(X9,X8)|r1_lattices(X6,X9,X7)))|~m1_subset_1(X7,u1_struct_0(X6))|(v2_struct_0(X6)|~l3_lattices(X6)))&((m1_subset_1(esk1_3(X6,X7,X10),u1_struct_0(X6))|r4_lattice3(X6,X7,X10)|~m1_subset_1(X7,u1_struct_0(X6))|(v2_struct_0(X6)|~l3_lattices(X6)))&((r2_hidden(esk1_3(X6,X7,X10),X10)|r4_lattice3(X6,X7,X10)|~m1_subset_1(X7,u1_struct_0(X6))|(v2_struct_0(X6)|~l3_lattices(X6)))&(~r1_lattices(X6,esk1_3(X6,X7,X10),X7)|r4_lattice3(X6,X7,X10)|~m1_subset_1(X7,u1_struct_0(X6))|(v2_struct_0(X6)|~l3_lattices(X6)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.20/0.40  cnf(c_0_20, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_21, negated_conjecture, (k15_lattice3(esk6_0,a_2_5_lattice3(esk6_0,X1))=k15_lattice3(esk6_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.20/0.40  fof(c_0_22, plain, ![X35, X36, X37]:((r3_lattices(X35,X36,k15_lattice3(X35,X37))|~r2_hidden(X36,X37)|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)))&(r3_lattices(X35,k16_lattice3(X35,X37),X36)|~r2_hidden(X36,X37)|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).
% 0.20/0.40  cnf(c_0_23, plain, (r2_hidden(X3,a_2_2_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r4_lattice3(X2,X1,X4)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_24, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_25, negated_conjecture, (m1_subset_1(k15_lattice3(esk6_0,X1),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_16])]), c_0_17])).
% 0.20/0.40  fof(c_0_26, plain, ![X33, X34]:(v2_struct_0(X33)|~v10_lattices(X33)|~v4_lattice3(X33)|~l3_lattices(X33)|k15_lattice3(X33,X34)=k16_lattice3(X33,a_2_2_lattice3(X33,X34))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_lattice3])])])])).
% 0.20/0.40  cnf(c_0_27, plain, (r3_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  cnf(c_0_28, plain, (r2_hidden(X1,a_2_2_lattice3(X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_23])).
% 0.20/0.40  cnf(c_0_29, negated_conjecture, (r4_lattice3(esk6_0,k15_lattice3(esk6_0,X1),X2)|m1_subset_1(esk1_3(esk6_0,k15_lattice3(esk6_0,X1),X2),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_16])]), c_0_17])).
% 0.20/0.40  cnf(c_0_30, plain, (v2_struct_0(X1)|k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_31, negated_conjecture, (r3_lattices(esk6_0,k16_lattice3(esk6_0,X1),k15_lattice3(esk6_0,X2))|~r2_hidden(k15_lattice3(esk6_0,X2),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_25]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.20/0.40  cnf(c_0_32, negated_conjecture, (r2_hidden(k15_lattice3(esk6_0,X1),a_2_2_lattice3(esk6_0,X2))|m1_subset_1(esk1_3(esk6_0,k15_lattice3(esk6_0,X1),X2),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_14]), c_0_15]), c_0_25]), c_0_16])]), c_0_17])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (k16_lattice3(esk6_0,a_2_2_lattice3(esk6_0,X1))=k15_lattice3(esk6_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (~r3_lattices(esk6_0,k15_lattice3(esk6_0,esk7_0),k15_lattice3(esk6_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_35, negated_conjecture, (r3_lattices(esk6_0,k15_lattice3(esk6_0,X1),k15_lattice3(esk6_0,X2))|m1_subset_1(esk1_3(esk6_0,k15_lattice3(esk6_0,X2),X1),u1_struct_0(esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.20/0.40  cnf(c_0_36, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  fof(c_0_37, plain, ![X12, X13, X14, X15]:(((r4_lattice3(X12,X14,X13)|X14!=k15_lattice3(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|(v2_struct_0(X12)|~v10_lattices(X12)|~v4_lattice3(X12)|~l3_lattices(X12))|(v2_struct_0(X12)|~l3_lattices(X12)))&(~m1_subset_1(X15,u1_struct_0(X12))|(~r4_lattice3(X12,X15,X13)|r1_lattices(X12,X14,X15))|X14!=k15_lattice3(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|(v2_struct_0(X12)|~v10_lattices(X12)|~v4_lattice3(X12)|~l3_lattices(X12))|(v2_struct_0(X12)|~l3_lattices(X12))))&((m1_subset_1(esk2_3(X12,X13,X14),u1_struct_0(X12))|~r4_lattice3(X12,X14,X13)|X14=k15_lattice3(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|(v2_struct_0(X12)|~v10_lattices(X12)|~v4_lattice3(X12)|~l3_lattices(X12))|(v2_struct_0(X12)|~l3_lattices(X12)))&((r4_lattice3(X12,esk2_3(X12,X13,X14),X13)|~r4_lattice3(X12,X14,X13)|X14=k15_lattice3(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|(v2_struct_0(X12)|~v10_lattices(X12)|~v4_lattice3(X12)|~l3_lattices(X12))|(v2_struct_0(X12)|~l3_lattices(X12)))&(~r1_lattices(X12,X14,esk2_3(X12,X13,X14))|~r4_lattice3(X12,X14,X13)|X14=k15_lattice3(X12,X13)|~m1_subset_1(X14,u1_struct_0(X12))|(v2_struct_0(X12)|~v10_lattices(X12)|~v4_lattice3(X12)|~l3_lattices(X12))|(v2_struct_0(X12)|~l3_lattices(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.20/0.40  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk9_1(X1),u1_struct_0(esk6_0))|~r2_hidden(X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_3(esk6_0,k15_lattice3(esk6_0,X1),X2),X2)|r4_lattice3(esk6_0,k15_lattice3(esk6_0,X1),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_25]), c_0_16])]), c_0_17])).
% 0.20/0.40  cnf(c_0_41, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X1)|X2!=k15_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.40  fof(c_0_42, plain, ![X25, X26, X27, X30, X31, X32]:((((m1_subset_1(esk4_3(X25,X26,X27),u1_struct_0(X26))|~r2_hidden(X25,a_2_5_lattice3(X26,X27))|(v2_struct_0(X26)|~v10_lattices(X26)|~v4_lattice3(X26)|~l3_lattices(X26)))&(X25=esk4_3(X25,X26,X27)|~r2_hidden(X25,a_2_5_lattice3(X26,X27))|(v2_struct_0(X26)|~v10_lattices(X26)|~v4_lattice3(X26)|~l3_lattices(X26))))&(((m1_subset_1(esk5_3(X25,X26,X27),u1_struct_0(X26))|~r2_hidden(X25,a_2_5_lattice3(X26,X27))|(v2_struct_0(X26)|~v10_lattices(X26)|~v4_lattice3(X26)|~l3_lattices(X26)))&(r3_lattices(X26,esk4_3(X25,X26,X27),esk5_3(X25,X26,X27))|~r2_hidden(X25,a_2_5_lattice3(X26,X27))|(v2_struct_0(X26)|~v10_lattices(X26)|~v4_lattice3(X26)|~l3_lattices(X26))))&(r2_hidden(esk5_3(X25,X26,X27),X27)|~r2_hidden(X25,a_2_5_lattice3(X26,X27))|(v2_struct_0(X26)|~v10_lattices(X26)|~v4_lattice3(X26)|~l3_lattices(X26)))))&(~m1_subset_1(X31,u1_struct_0(X26))|X25!=X31|(~m1_subset_1(X32,u1_struct_0(X26))|~r3_lattices(X26,X31,X32)|~r2_hidden(X32,X30))|r2_hidden(X25,a_2_5_lattice3(X26,X30))|(v2_struct_0(X26)|~v10_lattices(X26)|~v4_lattice3(X26)|~l3_lattices(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_5_lattice3])])])])])])])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (r3_lattices(esk6_0,X1,esk9_1(X1))|~r2_hidden(X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk9_1(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0)),u1_struct_0(esk6_0))|~r2_hidden(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_3(esk6_0,k15_lattice3(esk6_0,X1),X2),X2)|r2_hidden(k15_lattice3(esk6_0,X1),a_2_2_lattice3(esk6_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_40]), c_0_14]), c_0_15]), c_0_25]), c_0_16])]), c_0_17])).
% 0.20/0.40  cnf(c_0_46, plain, (v2_struct_0(X1)|r4_lattice3(X1,X2,X3)|X2!=k15_lattice3(X1,X3)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_41])).
% 0.20/0.40  cnf(c_0_47, plain, (r2_hidden(X3,a_2_5_lattice3(X2,X5))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~m1_subset_1(X4,u1_struct_0(X2))|~r3_lattices(X2,X1,X4)|~r2_hidden(X4,X5)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (r3_lattices(esk6_0,esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),esk9_1(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0)))|~r2_hidden(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_43, c_0_39])).
% 0.20/0.40  cnf(c_0_49, negated_conjecture, (r2_hidden(k15_lattice3(esk6_0,esk8_0),a_2_2_lattice3(esk6_0,esk7_0))|m1_subset_1(esk9_1(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0)),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.40  cnf(c_0_50, plain, (r1_lattices(X1,X4,X2)|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_51, plain, (r4_lattice3(X1,k15_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_46]), c_0_20])).
% 0.20/0.40  cnf(c_0_52, plain, (r2_hidden(X1,a_2_5_lattice3(X2,X3))|v2_struct_0(X2)|~r3_lattices(X2,X1,X4)|~v4_lattice3(X2)|~v10_lattices(X2)|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_47])).
% 0.20/0.40  cnf(c_0_53, negated_conjecture, (r3_lattices(esk6_0,esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),esk9_1(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0)))|r2_hidden(k15_lattice3(esk6_0,esk8_0),a_2_2_lattice3(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_48, c_0_45])).
% 0.20/0.40  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk9_1(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0)),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_49]), c_0_33]), c_0_34])).
% 0.20/0.40  cnf(c_0_55, plain, (r1_lattices(X1,X2,k15_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~r2_hidden(X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_20])).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (r2_hidden(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),a_2_5_lattice3(esk6_0,X1))|r2_hidden(k15_lattice3(esk6_0,esk8_0),a_2_2_lattice3(esk6_0,esk7_0))|~r2_hidden(esk9_1(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0)),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_14]), c_0_15]), c_0_54]), c_0_39]), c_0_16])]), c_0_17])).
% 0.20/0.40  cnf(c_0_57, negated_conjecture, (r2_hidden(esk9_1(X1),esk8_0)|~r2_hidden(X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_58, negated_conjecture, (r1_lattices(esk6_0,esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),k15_lattice3(esk6_0,X1))|~r2_hidden(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_39]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),a_2_5_lattice3(esk6_0,esk8_0))|r2_hidden(k15_lattice3(esk6_0,esk8_0),a_2_2_lattice3(esk6_0,esk7_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_39])]), c_0_45])).
% 0.20/0.40  cnf(c_0_60, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,esk1_3(X1,X2,X3),X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, (r1_lattices(esk6_0,esk1_3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0),k15_lattice3(esk6_0,esk8_0))|r2_hidden(k15_lattice3(esk6_0,esk8_0),a_2_2_lattice3(esk6_0,esk7_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_21])).
% 0.20/0.40  cnf(c_0_62, negated_conjecture, (r2_hidden(k15_lattice3(esk6_0,esk8_0),a_2_2_lattice3(esk6_0,esk7_0))|r4_lattice3(esk6_0,k15_lattice3(esk6_0,esk8_0),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_25]), c_0_16])]), c_0_17])).
% 0.20/0.40  cnf(c_0_63, negated_conjecture, (r2_hidden(k15_lattice3(esk6_0,esk8_0),a_2_2_lattice3(esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_62]), c_0_14]), c_0_15]), c_0_25]), c_0_16])]), c_0_17])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_63]), c_0_33]), c_0_34]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 65
% 0.20/0.40  # Proof object clause steps            : 46
% 0.20/0.40  # Proof object formula steps           : 19
% 0.20/0.40  # Proof object conjectures             : 33
% 0.20/0.40  # Proof object clause conjectures      : 30
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 19
% 0.20/0.40  # Proof object initial formulas used   : 9
% 0.20/0.40  # Proof object generating inferences   : 23
% 0.20/0.40  # Proof object simplifying inferences  : 71
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 9
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 33
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 33
% 0.20/0.40  # Processed clauses                    : 304
% 0.20/0.40  # ...of these trivial                  : 18
% 0.20/0.40  # ...subsumed                          : 58
% 0.20/0.40  # ...remaining for further processing  : 228
% 0.20/0.40  # Other redundant clauses eliminated   : 4
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 16
% 0.20/0.40  # Generated clauses                    : 978
% 0.20/0.40  # ...of the previous two non-trivial   : 943
% 0.20/0.40  # Contextual simplify-reflections      : 5
% 0.20/0.40  # Paramodulations                      : 974
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 4
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
% 0.20/0.40  # Current number of processed clauses  : 175
% 0.20/0.40  #    Positive orientable unit clauses  : 50
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 2
% 0.20/0.40  #    Non-unit-clauses                  : 123
% 0.20/0.40  # Current number of unprocessed clauses: 670
% 0.20/0.40  # ...number of literals in the above   : 1211
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 49
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 1932
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 1499
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 63
% 0.20/0.40  # Unit Clause-clause subsumption calls : 159
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 151
% 0.20/0.40  # BW rewrite match successes           : 4
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 27944
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.057 s
% 0.20/0.40  # System time              : 0.004 s
% 0.20/0.40  # Total time               : 0.061 s
% 0.20/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
