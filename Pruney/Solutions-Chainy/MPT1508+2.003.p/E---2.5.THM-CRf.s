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
% DateTime   : Thu Dec  3 11:15:02 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 314 expanded)
%              Number of clauses        :   44 ( 104 expanded)
%              Number of leaves         :    9 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  294 (2008 expanded)
%              Number of equality atoms :   19 ( 193 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   28 (   3 average)
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

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

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

fof(dt_k16_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(t26_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_lattices(X1,X2,X3)
                  & r1_lattices(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

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

fof(d22_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] : k16_lattice3(X1,X2) = k15_lattice3(X1,a_2_1_lattice3(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d22_lattice3)).

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
    ! [X6] :
      ( ( l1_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( l2_lattices(X6)
        | ~ l3_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v10_lattices(esk2_0)
    & v4_lattice3(esk2_0)
    & l3_lattices(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & r2_hidden(esk3_0,esk4_0)
    & r3_lattice3(esk2_0,esk3_0,esk4_0)
    & k16_lattice3(esk2_0,esk4_0) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
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

fof(c_0_13,plain,(
    ! [X7,X8,X9] :
      ( ( ~ r3_lattices(X7,X8,X9)
        | r1_lattices(X7,X8,X9)
        | v2_struct_0(X7)
        | ~ v6_lattices(X7)
        | ~ v8_lattices(X7)
        | ~ v9_lattices(X7)
        | ~ l3_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7)) )
      & ( ~ r1_lattices(X7,X8,X9)
        | r3_lattices(X7,X8,X9)
        | v2_struct_0(X7)
        | ~ v6_lattices(X7)
        | ~ v8_lattices(X7)
        | ~ v9_lattices(X7)
        | ~ l3_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

fof(c_0_14,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ l3_lattices(X15)
      | m1_subset_1(k16_lattice3(X15,X16),u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

fof(c_0_15,plain,(
    ! [X10,X11,X12] :
      ( v2_struct_0(X10)
      | ~ v4_lattices(X10)
      | ~ l2_lattices(X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ r1_lattices(X10,X11,X12)
      | ~ r1_lattices(X10,X12,X11)
      | X11 = X12 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

cnf(c_0_16,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( l2_lattices(esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( v4_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_17])]),c_0_20])).

cnf(c_0_30,plain,
    ( r1_lattices(X1,X2,k16_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,k16_lattice3(X1,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( v9_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_17])]),c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( v8_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_17])]),c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( v6_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_19]),c_0_17])]),c_0_20])).

fof(c_0_34,plain,(
    ! [X17,X18,X19,X21,X22] :
      ( ( m1_subset_1(esk1_3(X17,X18,X19),u1_struct_0(X18))
        | ~ r2_hidden(X17,a_2_1_lattice3(X18,X19))
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( X17 = esk1_3(X17,X18,X19)
        | ~ r2_hidden(X17,a_2_1_lattice3(X18,X19))
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( r3_lattice3(X18,esk1_3(X17,X18,X19),X19)
        | ~ r2_hidden(X17,a_2_1_lattice3(X18,X19))
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X18))
        | X17 != X22
        | ~ r3_lattice3(X18,X22,X21)
        | r2_hidden(X17,a_2_1_lattice3(X18,X21))
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_lattice3])])])])])])])).

fof(c_0_35,plain,(
    ! [X23,X24,X25] :
      ( ( r3_lattices(X23,X24,k15_lattice3(X23,X25))
        | ~ r2_hidden(X24,X25)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v10_lattices(X23)
        | ~ v4_lattice3(X23)
        | ~ l3_lattices(X23) )
      & ( r3_lattices(X23,k16_lattice3(X23,X25),X24)
        | ~ r2_hidden(X24,X25)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ v10_lattices(X23)
        | ~ v4_lattice3(X23)
        | ~ l3_lattices(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

cnf(c_0_36,negated_conjecture,
    ( X1 = esk3_0
    | ~ r1_lattices(esk2_0,esk3_0,X1)
    | ~ r1_lattices(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_20]),c_0_28]),c_0_29])])).

cnf(c_0_37,negated_conjecture,
    ( r1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))
    | ~ r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_27]),c_0_31]),c_0_32]),c_0_33]),c_0_17])]),c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( r1_lattices(esk2_0,X1,esk3_0)
    | ~ r3_lattices(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_27]),c_0_17])]),c_0_20]),c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_39,plain,
    ( r2_hidden(X3,a_2_1_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattice3(X2,X1,X4)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r3_lattices(X1,k16_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( v4_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,negated_conjecture,
    ( k16_lattice3(esk2_0,X1) = esk3_0
    | ~ r1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)
    | ~ r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))
    | ~ m1_subset_1(k16_lattice3(esk2_0,X1),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)
    | ~ r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_22]),c_0_17])]),c_0_20])).

fof(c_0_44,plain,(
    ! [X13,X14] :
      ( v2_struct_0(X13)
      | ~ l3_lattices(X13)
      | k16_lattice3(X13,X14) = k15_lattice3(X13,a_2_1_lattice3(X13,X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d22_lattice3])])])])).

cnf(c_0_45,plain,
    ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,a_2_1_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r3_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,negated_conjecture,
    ( r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_27]),c_0_41]),c_0_19]),c_0_17])]),c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,negated_conjecture,
    ( k16_lattice3(esk2_0,X1) = esk3_0
    | ~ r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))
    | ~ r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)
    | ~ m1_subset_1(k16_lattice3(esk2_0,X1),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | k16_lattice3(X1,X2) = k15_lattice3(X1,a_2_1_lattice3(X1,X2))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( r3_lattices(esk2_0,esk3_0,k15_lattice3(esk2_0,X1))
    | ~ r2_hidden(esk3_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_27]),c_0_41]),c_0_19]),c_0_17])]),c_0_20])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_0,a_2_1_lattice3(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_27]),c_0_17])]),c_0_20])).

cnf(c_0_54,negated_conjecture,
    ( r3_lattices(esk2_0,k16_lattice3(esk2_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k16_lattice3(esk2_0,esk4_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_56,negated_conjecture,
    ( k15_lattice3(esk2_0,a_2_1_lattice3(esk2_0,X1)) = esk3_0
    | ~ r3_lattices(esk2_0,esk3_0,k15_lattice3(esk2_0,a_2_1_lattice3(esk2_0,X1)))
    | ~ r3_lattices(esk2_0,k15_lattice3(esk2_0,a_2_1_lattice3(esk2_0,X1)),esk3_0)
    | ~ m1_subset_1(k15_lattice3(esk2_0,a_2_1_lattice3(esk2_0,X1)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_17])]),c_0_20])).

cnf(c_0_57,negated_conjecture,
    ( r3_lattices(esk2_0,esk3_0,k15_lattice3(esk2_0,a_2_1_lattice3(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r3_lattices(esk2_0,k15_lattice3(esk2_0,a_2_1_lattice3(esk2_0,esk4_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_51]),c_0_17])]),c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( k15_lattice3(esk2_0,a_2_1_lattice3(esk2_0,esk4_0)) != esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_51]),c_0_17])]),c_0_20])).

cnf(c_0_60,negated_conjecture,
    ( ~ m1_subset_1(k15_lattice3(esk2_0,a_2_1_lattice3(esk2_0,esk4_0)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])]),c_0_59])).

cnf(c_0_61,plain,
    ( m1_subset_1(k15_lattice3(X1,a_2_1_lattice3(X1,X2)),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_17])]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.41  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.13/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.41  #
% 0.13/0.41  # Preprocessing time       : 0.046 s
% 0.13/0.41  # Presaturation interreduction done
% 0.13/0.41  
% 0.13/0.41  # Proof found!
% 0.13/0.41  # SZS status Theorem
% 0.13/0.41  # SZS output start CNFRefutation
% 0.13/0.41  fof(t42_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_lattice3)).
% 0.13/0.41  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.13/0.41  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.13/0.41  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.13/0.41  fof(dt_k16_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 0.13/0.41  fof(t26_lattices, axiom, ![X1]:(((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_lattices(X1,X2,X3)&r1_lattices(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_lattices)).
% 0.13/0.41  fof(fraenkel_a_2_1_lattice3, axiom, ![X1, X2, X3]:((~(v2_struct_0(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_1_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r3_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 0.13/0.41  fof(t38_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r2_hidden(X2,X3)=>(r3_lattices(X1,X2,k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 0.13/0.41  fof(d22_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:k16_lattice3(X1,X2)=k15_lattice3(X1,a_2_1_lattice3(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d22_lattice3)).
% 0.13/0.41  fof(c_0_9, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:((r2_hidden(X2,X3)&r3_lattice3(X1,X2,X3))=>k16_lattice3(X1,X3)=X2)))), inference(assume_negation,[status(cth)],[t42_lattice3])).
% 0.13/0.41  fof(c_0_10, plain, ![X6]:((l1_lattices(X6)|~l3_lattices(X6))&(l2_lattices(X6)|~l3_lattices(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.13/0.41  fof(c_0_11, negated_conjecture, ((((~v2_struct_0(esk2_0)&v10_lattices(esk2_0))&v4_lattice3(esk2_0))&l3_lattices(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&((r2_hidden(esk3_0,esk4_0)&r3_lattice3(esk2_0,esk3_0,esk4_0))&k16_lattice3(esk2_0,esk4_0)!=esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.13/0.41  fof(c_0_12, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.13/0.41  fof(c_0_13, plain, ![X7, X8, X9]:((~r3_lattices(X7,X8,X9)|r1_lattices(X7,X8,X9)|(v2_struct_0(X7)|~v6_lattices(X7)|~v8_lattices(X7)|~v9_lattices(X7)|~l3_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))))&(~r1_lattices(X7,X8,X9)|r3_lattices(X7,X8,X9)|(v2_struct_0(X7)|~v6_lattices(X7)|~v8_lattices(X7)|~v9_lattices(X7)|~l3_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.13/0.41  fof(c_0_14, plain, ![X15, X16]:(v2_struct_0(X15)|~l3_lattices(X15)|m1_subset_1(k16_lattice3(X15,X16),u1_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).
% 0.13/0.41  fof(c_0_15, plain, ![X10, X11, X12]:(v2_struct_0(X10)|~v4_lattices(X10)|~l2_lattices(X10)|(~m1_subset_1(X11,u1_struct_0(X10))|(~m1_subset_1(X12,u1_struct_0(X10))|(~r1_lattices(X10,X11,X12)|~r1_lattices(X10,X12,X11)|X11=X12)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).
% 0.13/0.41  cnf(c_0_16, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.41  cnf(c_0_17, negated_conjecture, (l3_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.41  cnf(c_0_18, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.41  cnf(c_0_19, negated_conjecture, (v10_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.41  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.41  cnf(c_0_21, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.41  cnf(c_0_22, plain, (v2_struct_0(X1)|m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.41  cnf(c_0_23, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.41  cnf(c_0_24, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.41  cnf(c_0_25, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.41  cnf(c_0_26, plain, (v2_struct_0(X1)|X2=X3|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattices(X1,X2,X3)|~r1_lattices(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.41  cnf(c_0_28, negated_conjecture, (l2_lattices(esk2_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.41  cnf(c_0_29, negated_conjecture, (v4_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_17])]), c_0_20])).
% 0.13/0.41  cnf(c_0_30, plain, (r1_lattices(X1,X2,k16_lattice3(X1,X3))|v2_struct_0(X1)|~r3_lattices(X1,X2,k16_lattice3(X1,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~v9_lattices(X1)|~v8_lattices(X1)|~v6_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.41  cnf(c_0_31, negated_conjecture, (v9_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_19]), c_0_17])]), c_0_20])).
% 0.13/0.41  cnf(c_0_32, negated_conjecture, (v8_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_19]), c_0_17])]), c_0_20])).
% 0.13/0.41  cnf(c_0_33, negated_conjecture, (v6_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_19]), c_0_17])]), c_0_20])).
% 0.13/0.41  fof(c_0_34, plain, ![X17, X18, X19, X21, X22]:((((m1_subset_1(esk1_3(X17,X18,X19),u1_struct_0(X18))|~r2_hidden(X17,a_2_1_lattice3(X18,X19))|(v2_struct_0(X18)|~l3_lattices(X18)))&(X17=esk1_3(X17,X18,X19)|~r2_hidden(X17,a_2_1_lattice3(X18,X19))|(v2_struct_0(X18)|~l3_lattices(X18))))&(r3_lattice3(X18,esk1_3(X17,X18,X19),X19)|~r2_hidden(X17,a_2_1_lattice3(X18,X19))|(v2_struct_0(X18)|~l3_lattices(X18))))&(~m1_subset_1(X22,u1_struct_0(X18))|X17!=X22|~r3_lattice3(X18,X22,X21)|r2_hidden(X17,a_2_1_lattice3(X18,X21))|(v2_struct_0(X18)|~l3_lattices(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_lattice3])])])])])])])).
% 0.13/0.41  fof(c_0_35, plain, ![X23, X24, X25]:((r3_lattices(X23,X24,k15_lattice3(X23,X25))|~r2_hidden(X24,X25)|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v10_lattices(X23)|~v4_lattice3(X23)|~l3_lattices(X23)))&(r3_lattices(X23,k16_lattice3(X23,X25),X24)|~r2_hidden(X24,X25)|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~v10_lattices(X23)|~v4_lattice3(X23)|~l3_lattices(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).
% 0.13/0.41  cnf(c_0_36, negated_conjecture, (X1=esk3_0|~r1_lattices(esk2_0,esk3_0,X1)|~r1_lattices(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_20]), c_0_28]), c_0_29])])).
% 0.13/0.41  cnf(c_0_37, negated_conjecture, (r1_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))|~r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_27]), c_0_31]), c_0_32]), c_0_33]), c_0_17])]), c_0_20])).
% 0.13/0.41  cnf(c_0_38, negated_conjecture, (r1_lattices(esk2_0,X1,esk3_0)|~r3_lattices(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_27]), c_0_17])]), c_0_20]), c_0_31]), c_0_32]), c_0_33])])).
% 0.13/0.41  cnf(c_0_39, plain, (r2_hidden(X3,a_2_1_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r3_lattice3(X2,X1,X4)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.41  cnf(c_0_40, plain, (r3_lattices(X1,k16_lattice3(X1,X2),X3)|v2_struct_0(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.41  cnf(c_0_41, negated_conjecture, (v4_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.41  cnf(c_0_42, negated_conjecture, (k16_lattice3(esk2_0,X1)=esk3_0|~r1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)|~r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))|~m1_subset_1(k16_lattice3(esk2_0,X1),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.41  cnf(c_0_43, negated_conjecture, (r1_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)|~r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_22]), c_0_17])]), c_0_20])).
% 0.13/0.41  fof(c_0_44, plain, ![X13, X14]:(v2_struct_0(X13)|~l3_lattices(X13)|k16_lattice3(X13,X14)=k15_lattice3(X13,a_2_1_lattice3(X13,X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d22_lattice3])])])])).
% 0.13/0.41  cnf(c_0_45, plain, (r3_lattices(X1,X2,k15_lattice3(X1,X3))|v2_struct_0(X1)|~r2_hidden(X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.41  cnf(c_0_46, plain, (r2_hidden(X1,a_2_1_lattice3(X2,X3))|v2_struct_0(X2)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_39])).
% 0.13/0.41  cnf(c_0_47, negated_conjecture, (r3_lattice3(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.41  cnf(c_0_48, negated_conjecture, (r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)|~r2_hidden(esk3_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_27]), c_0_41]), c_0_19]), c_0_17])]), c_0_20])).
% 0.13/0.41  cnf(c_0_49, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.41  cnf(c_0_50, negated_conjecture, (k16_lattice3(esk2_0,X1)=esk3_0|~r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))|~r3_lattices(esk2_0,k16_lattice3(esk2_0,X1),esk3_0)|~m1_subset_1(k16_lattice3(esk2_0,X1),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.41  cnf(c_0_51, plain, (v2_struct_0(X1)|k16_lattice3(X1,X2)=k15_lattice3(X1,a_2_1_lattice3(X1,X2))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.41  cnf(c_0_52, negated_conjecture, (r3_lattices(esk2_0,esk3_0,k15_lattice3(esk2_0,X1))|~r2_hidden(esk3_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_27]), c_0_41]), c_0_19]), c_0_17])]), c_0_20])).
% 0.13/0.41  cnf(c_0_53, negated_conjecture, (r2_hidden(esk3_0,a_2_1_lattice3(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_27]), c_0_17])]), c_0_20])).
% 0.13/0.41  cnf(c_0_54, negated_conjecture, (r3_lattices(esk2_0,k16_lattice3(esk2_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.41  cnf(c_0_55, negated_conjecture, (k16_lattice3(esk2_0,esk4_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.41  cnf(c_0_56, negated_conjecture, (k15_lattice3(esk2_0,a_2_1_lattice3(esk2_0,X1))=esk3_0|~r3_lattices(esk2_0,esk3_0,k15_lattice3(esk2_0,a_2_1_lattice3(esk2_0,X1)))|~r3_lattices(esk2_0,k15_lattice3(esk2_0,a_2_1_lattice3(esk2_0,X1)),esk3_0)|~m1_subset_1(k15_lattice3(esk2_0,a_2_1_lattice3(esk2_0,X1)),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_17])]), c_0_20])).
% 0.13/0.41  cnf(c_0_57, negated_conjecture, (r3_lattices(esk2_0,esk3_0,k15_lattice3(esk2_0,a_2_1_lattice3(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.41  cnf(c_0_58, negated_conjecture, (r3_lattices(esk2_0,k15_lattice3(esk2_0,a_2_1_lattice3(esk2_0,esk4_0)),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_51]), c_0_17])]), c_0_20])).
% 0.13/0.41  cnf(c_0_59, negated_conjecture, (k15_lattice3(esk2_0,a_2_1_lattice3(esk2_0,esk4_0))!=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_51]), c_0_17])]), c_0_20])).
% 0.13/0.41  cnf(c_0_60, negated_conjecture, (~m1_subset_1(k15_lattice3(esk2_0,a_2_1_lattice3(esk2_0,esk4_0)),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])]), c_0_59])).
% 0.13/0.41  cnf(c_0_61, plain, (m1_subset_1(k15_lattice3(X1,a_2_1_lattice3(X1,X2)),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_22, c_0_51])).
% 0.13/0.41  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_17])]), c_0_20]), ['proof']).
% 0.13/0.41  # SZS output end CNFRefutation
% 0.13/0.41  # Proof object total steps             : 63
% 0.13/0.41  # Proof object clause steps            : 44
% 0.13/0.41  # Proof object formula steps           : 19
% 0.13/0.41  # Proof object conjectures             : 32
% 0.13/0.41  # Proof object clause conjectures      : 29
% 0.13/0.41  # Proof object formula conjectures     : 3
% 0.13/0.41  # Proof object initial clauses used    : 20
% 0.13/0.41  # Proof object initial formulas used   : 9
% 0.13/0.41  # Proof object generating inferences   : 23
% 0.13/0.41  # Proof object simplifying inferences  : 62
% 0.13/0.41  # Training examples: 0 positive, 0 negative
% 0.13/0.41  # Parsed axioms                        : 9
% 0.13/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.41  # Initial clauses                      : 28
% 0.13/0.41  # Removed in clause preprocessing      : 1
% 0.13/0.41  # Initial clauses in saturation        : 27
% 0.13/0.41  # Processed clauses                    : 107
% 0.13/0.41  # ...of these trivial                  : 0
% 0.13/0.41  # ...subsumed                          : 7
% 0.13/0.41  # ...remaining for further processing  : 100
% 0.13/0.41  # Other redundant clauses eliminated   : 1
% 0.13/0.41  # Clauses deleted for lack of memory   : 0
% 0.13/0.41  # Backward-subsumed                    : 0
% 0.13/0.41  # Backward-rewritten                   : 0
% 0.13/0.41  # Generated clauses                    : 80
% 0.13/0.41  # ...of the previous two non-trivial   : 72
% 0.13/0.41  # Contextual simplify-reflections      : 1
% 0.13/0.41  # Paramodulations                      : 79
% 0.13/0.41  # Factorizations                       : 0
% 0.13/0.41  # Equation resolutions                 : 1
% 0.13/0.41  # Propositional unsat checks           : 0
% 0.13/0.41  #    Propositional check models        : 0
% 0.13/0.41  #    Propositional check unsatisfiable : 0
% 0.13/0.41  #    Propositional clauses             : 0
% 0.13/0.41  #    Propositional clauses after purity: 0
% 0.13/0.41  #    Propositional unsat core size     : 0
% 0.13/0.41  #    Propositional preprocessing time  : 0.000
% 0.13/0.41  #    Propositional encoding time       : 0.000
% 0.13/0.41  #    Propositional solver time         : 0.000
% 0.13/0.41  #    Success case prop preproc time    : 0.000
% 0.13/0.41  #    Success case prop encoding time   : 0.000
% 0.13/0.41  #    Success case prop solver time     : 0.000
% 0.13/0.41  # Current number of processed clauses  : 72
% 0.13/0.41  #    Positive orientable unit clauses  : 21
% 0.13/0.41  #    Positive unorientable unit clauses: 0
% 0.13/0.41  #    Negative unit clauses             : 4
% 0.13/0.41  #    Non-unit-clauses                  : 47
% 0.13/0.41  # Current number of unprocessed clauses: 19
% 0.13/0.41  # ...number of literals in the above   : 137
% 0.13/0.41  # Current number of archived formulas  : 0
% 0.13/0.41  # Current number of archived clauses   : 27
% 0.13/0.41  # Clause-clause subsumption calls (NU) : 860
% 0.13/0.41  # Rec. Clause-clause subsumption calls : 232
% 0.13/0.41  # Non-unit clause-clause subsumptions  : 8
% 0.13/0.41  # Unit Clause-clause subsumption calls : 8
% 0.13/0.41  # Rewrite failures with RHS unbound    : 0
% 0.13/0.41  # BW rewrite match attempts            : 4
% 0.13/0.41  # BW rewrite match successes           : 0
% 0.13/0.41  # Condensation attempts                : 0
% 0.13/0.41  # Condensation successes               : 0
% 0.13/0.41  # Termbank termtop insertions          : 4682
% 0.13/0.41  
% 0.13/0.41  # -------------------------------------------------
% 0.13/0.41  # User time                : 0.055 s
% 0.13/0.41  # System time              : 0.006 s
% 0.13/0.41  # Total time               : 0.062 s
% 0.13/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
