%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattice3__t45_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:55 EDT 2019

% Result     : Theorem 0.75s
% Output     : CNFRefutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   92 (2633 expanded)
%              Number of clauses        :   71 ( 840 expanded)
%              Number of leaves         :   10 ( 643 expanded)
%              Depth                    :   26
%              Number of atoms          :  511 (16845 expanded)
%              Number of equality atoms :   49 (3253 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/lattice3__t45_lattice3.p',t45_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/lattice3__t45_lattice3.p',reflexivity_r3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattice3__t45_lattice3.p',cc1_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattice3__t45_lattice3.p',d17_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/lattice3__t45_lattice3.p',fraenkel_a_2_3_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/lattice3__t45_lattice3.p',t41_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/lattice3__t45_lattice3.p',redefinition_r3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattice3__t45_lattice3.p',d16_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/lattice3__t45_lattice3.p',fraenkel_a_2_4_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/lattice3__t45_lattice3.p',t42_lattice3)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X53,X54,X55] :
      ( v2_struct_0(X53)
      | ~ v6_lattices(X53)
      | ~ v8_lattices(X53)
      | ~ v9_lattices(X53)
      | ~ l3_lattices(X53)
      | ~ m1_subset_1(X54,u1_struct_0(X53))
      | ~ m1_subset_1(X55,u1_struct_0(X53))
      | r3_lattices(X53,X54,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_lattices])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v4_lattice3(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ( esk2_0 != k15_lattice3(esk1_0,a_2_3_lattice3(esk1_0,esk2_0))
      | esk2_0 != k16_lattice3(esk1_0,a_2_4_lattice3(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,X2,X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r3_lattices(esk1_0,X1,X1)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])]),c_0_16])).

fof(c_0_18,plain,(
    ! [X74] :
      ( ( ~ v2_struct_0(X74)
        | v2_struct_0(X74)
        | ~ v10_lattices(X74)
        | ~ l3_lattices(X74) )
      & ( v4_lattices(X74)
        | v2_struct_0(X74)
        | ~ v10_lattices(X74)
        | ~ l3_lattices(X74) )
      & ( v5_lattices(X74)
        | v2_struct_0(X74)
        | ~ v10_lattices(X74)
        | ~ l3_lattices(X74) )
      & ( v6_lattices(X74)
        | v2_struct_0(X74)
        | ~ v10_lattices(X74)
        | ~ l3_lattices(X74) )
      & ( v7_lattices(X74)
        | v2_struct_0(X74)
        | ~ v10_lattices(X74)
        | ~ l3_lattices(X74) )
      & ( v8_lattices(X74)
        | v2_struct_0(X74)
        | ~ v10_lattices(X74)
        | ~ l3_lattices(X74) )
      & ( v9_lattices(X74)
        | v2_struct_0(X74)
        | ~ v10_lattices(X74)
        | ~ l3_lattices(X74) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_19,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk2_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_20,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_22,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( ~ r4_lattice3(X15,X16,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r2_hidden(X18,X17)
        | r1_lattices(X15,X18,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( m1_subset_1(esk4_3(X15,X16,X19),u1_struct_0(X15))
        | r4_lattice3(X15,X16,X19)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( r2_hidden(esk4_3(X15,X16,X19),X19)
        | r4_lattice3(X15,X16,X19)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( ~ r1_lattices(X15,esk4_3(X15,X16,X19),X16)
        | r4_lattice3(X15,X16,X19)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

fof(c_0_23,plain,(
    ! [X40,X41,X42,X44] :
      ( ( m1_subset_1(esk11_3(X40,X41,X42),u1_struct_0(X41))
        | ~ r2_hidden(X40,a_2_3_lattice3(X41,X42))
        | v2_struct_0(X41)
        | ~ v10_lattices(X41)
        | ~ v4_lattice3(X41)
        | ~ l3_lattices(X41)
        | ~ m1_subset_1(X42,u1_struct_0(X41)) )
      & ( X40 = esk11_3(X40,X41,X42)
        | ~ r2_hidden(X40,a_2_3_lattice3(X41,X42))
        | v2_struct_0(X41)
        | ~ v10_lattices(X41)
        | ~ v4_lattice3(X41)
        | ~ l3_lattices(X41)
        | ~ m1_subset_1(X42,u1_struct_0(X41)) )
      & ( r3_lattices(X41,esk11_3(X40,X41,X42),X42)
        | ~ r2_hidden(X40,a_2_3_lattice3(X41,X42))
        | v2_struct_0(X41)
        | ~ v10_lattices(X41)
        | ~ v4_lattice3(X41)
        | ~ l3_lattices(X41)
        | ~ m1_subset_1(X42,u1_struct_0(X41)) )
      & ( ~ m1_subset_1(X44,u1_struct_0(X41))
        | X40 != X44
        | ~ r3_lattices(X41,X44,X42)
        | r2_hidden(X40,a_2_3_lattice3(X41,X42))
        | v2_struct_0(X41)
        | ~ v10_lattices(X41)
        | ~ v4_lattice3(X41)
        | ~ l3_lattices(X41)
        | ~ m1_subset_1(X42,u1_struct_0(X41)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_3_lattice3])])])])])])).

cnf(c_0_24,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk2_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_15]),c_0_21])]),c_0_16])).

cnf(c_0_25,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X63,X64,X65] :
      ( v2_struct_0(X63)
      | ~ v10_lattices(X63)
      | ~ v4_lattice3(X63)
      | ~ l3_lattices(X63)
      | ~ m1_subset_1(X64,u1_struct_0(X63))
      | ~ r2_hidden(X64,X65)
      | ~ r4_lattice3(X63,X64,X65)
      | k15_lattice3(X63,X65) = X64 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_lattice3])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(X3,a_2_3_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattices(X2,X1,X4)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk2_0)
    | ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_15]),c_0_21])]),c_0_16])).

cnf(c_0_30,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | k15_lattice3(X1,X3) = X2
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X3)
    | ~ r4_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r4_lattice3(esk1_0,esk2_0,X1)
    | r2_hidden(esk4_3(esk1_0,esk2_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( v4_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,a_2_3_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattices(X2,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_15]),c_0_21])]),c_0_16])).

cnf(c_0_36,plain,
    ( r3_lattices(X1,esk11_3(X2,X1,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_3_lattice3(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( k15_lattice3(esk1_0,X1) = esk2_0
    | r2_hidden(esk4_3(esk1_0,esk2_0,X1),X1)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_14]),c_0_15]),c_0_33]),c_0_21])]),c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk2_0,a_2_3_lattice3(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_14]),c_0_15]),c_0_33]),c_0_21])]),c_0_16])).

cnf(c_0_39,plain,
    ( X1 = esk11_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_3_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,negated_conjecture,
    ( r3_lattices(esk1_0,esk11_3(X1,esk1_0,esk2_0),esk2_0)
    | ~ r2_hidden(X1,a_2_3_lattice3(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_14]),c_0_15]),c_0_33]),c_0_21])]),c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( k15_lattice3(esk1_0,a_2_3_lattice3(esk1_0,esk2_0)) = esk2_0
    | r2_hidden(esk4_3(esk1_0,esk2_0,a_2_3_lattice3(esk1_0,esk2_0)),a_2_3_lattice3(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( esk11_3(X1,esk1_0,esk2_0) = X1
    | ~ r2_hidden(X1,a_2_3_lattice3(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_14]),c_0_15]),c_0_33]),c_0_21])]),c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( r4_lattice3(esk1_0,esk2_0,X1)
    | m1_subset_1(esk4_3(esk1_0,esk2_0,X1),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_14]),c_0_15])]),c_0_16])).

fof(c_0_45,plain,(
    ! [X50,X51,X52] :
      ( ( ~ r3_lattices(X50,X51,X52)
        | r1_lattices(X50,X51,X52)
        | v2_struct_0(X50)
        | ~ v6_lattices(X50)
        | ~ v8_lattices(X50)
        | ~ v9_lattices(X50)
        | ~ l3_lattices(X50)
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | ~ m1_subset_1(X52,u1_struct_0(X50)) )
      & ( ~ r1_lattices(X50,X51,X52)
        | r3_lattices(X50,X51,X52)
        | v2_struct_0(X50)
        | ~ v6_lattices(X50)
        | ~ v8_lattices(X50)
        | ~ v9_lattices(X50)
        | ~ l3_lattices(X50)
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | ~ m1_subset_1(X52,u1_struct_0(X50)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_46,negated_conjecture,
    ( k15_lattice3(esk1_0,a_2_3_lattice3(esk1_0,esk2_0)) = esk2_0
    | r3_lattices(esk1_0,esk11_3(esk4_3(esk1_0,esk2_0,a_2_3_lattice3(esk1_0,esk2_0)),esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( esk11_3(esk4_3(esk1_0,esk2_0,a_2_3_lattice3(esk1_0,esk2_0)),esk1_0,esk2_0) = esk4_3(esk1_0,esk2_0,a_2_3_lattice3(esk1_0,esk2_0))
    | k15_lattice3(esk1_0,a_2_3_lattice3(esk1_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k15_lattice3(esk1_0,X1) = esk2_0
    | m1_subset_1(esk4_3(esk1_0,esk2_0,X1),u1_struct_0(esk1_0))
    | ~ r2_hidden(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_44]),c_0_14]),c_0_15]),c_0_33]),c_0_21])]),c_0_16])).

cnf(c_0_49,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( k15_lattice3(esk1_0,a_2_3_lattice3(esk1_0,esk2_0)) = esk2_0
    | r3_lattices(esk1_0,esk4_3(esk1_0,esk2_0,a_2_3_lattice3(esk1_0,esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( k15_lattice3(esk1_0,a_2_3_lattice3(esk1_0,esk2_0)) = esk2_0
    | m1_subset_1(esk4_3(esk1_0,esk2_0,a_2_3_lattice3(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_38])).

fof(c_0_52,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r3_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ r2_hidden(X12,X11)
        | r1_lattices(X9,X10,X12)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk3_3(X9,X10,X13),u1_struct_0(X9))
        | r3_lattice3(X9,X10,X13)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( r2_hidden(esk3_3(X9,X10,X13),X13)
        | r3_lattice3(X9,X10,X13)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( ~ r1_lattices(X9,X10,esk3_3(X9,X10,X13))
        | r3_lattice3(X9,X10,X13)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

fof(c_0_53,plain,(
    ! [X45,X46,X47,X49] :
      ( ( m1_subset_1(esk12_3(X45,X46,X47),u1_struct_0(X46))
        | ~ r2_hidden(X45,a_2_4_lattice3(X46,X47))
        | v2_struct_0(X46)
        | ~ v10_lattices(X46)
        | ~ v4_lattice3(X46)
        | ~ l3_lattices(X46)
        | ~ m1_subset_1(X47,u1_struct_0(X46)) )
      & ( X45 = esk12_3(X45,X46,X47)
        | ~ r2_hidden(X45,a_2_4_lattice3(X46,X47))
        | v2_struct_0(X46)
        | ~ v10_lattices(X46)
        | ~ v4_lattice3(X46)
        | ~ l3_lattices(X46)
        | ~ m1_subset_1(X47,u1_struct_0(X46)) )
      & ( r3_lattices(X46,X47,esk12_3(X45,X46,X47))
        | ~ r2_hidden(X45,a_2_4_lattice3(X46,X47))
        | v2_struct_0(X46)
        | ~ v10_lattices(X46)
        | ~ v4_lattice3(X46)
        | ~ l3_lattices(X46)
        | ~ m1_subset_1(X47,u1_struct_0(X46)) )
      & ( ~ m1_subset_1(X49,u1_struct_0(X46))
        | X45 != X49
        | ~ r3_lattices(X46,X47,X49)
        | r2_hidden(X45,a_2_4_lattice3(X46,X47))
        | v2_struct_0(X46)
        | ~ v10_lattices(X46)
        | ~ v4_lattice3(X46)
        | ~ l3_lattices(X46)
        | ~ m1_subset_1(X47,u1_struct_0(X46)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_4_lattice3])])])])])])).

cnf(c_0_54,negated_conjecture,
    ( k15_lattice3(esk1_0,a_2_3_lattice3(esk1_0,esk2_0)) = esk2_0
    | r1_lattices(esk1_0,esk4_3(esk1_0,esk2_0,a_2_3_lattice3(esk1_0,esk2_0)),esk2_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_14]),c_0_15])]),c_0_16]),c_0_51])).

fof(c_0_55,plain,(
    ! [X66,X67,X68] :
      ( v2_struct_0(X66)
      | ~ v10_lattices(X66)
      | ~ v4_lattice3(X66)
      | ~ l3_lattices(X66)
      | ~ m1_subset_1(X67,u1_struct_0(X66))
      | ~ r2_hidden(X67,X68)
      | ~ r3_lattice3(X66,X67,X68)
      | k16_lattice3(X66,X68) = X67 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_lattice3])])])])).

cnf(c_0_56,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,plain,
    ( r2_hidden(X3,a_2_4_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattices(X2,X4,X1)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( k15_lattice3(esk1_0,a_2_3_lattice3(esk1_0,esk2_0)) = esk2_0
    | r1_lattices(esk1_0,esk4_3(esk1_0,esk2_0,a_2_3_lattice3(esk1_0,esk2_0)),esk2_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_20]),c_0_15]),c_0_21])]),c_0_16])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | k16_lattice3(X1,X3) = X2
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X3)
    | ~ r3_lattice3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r3_lattice3(esk1_0,esk2_0,X1)
    | r2_hidden(esk3_3(esk1_0,esk2_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,a_2_4_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattices(X2,X3,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l3_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( k15_lattice3(esk1_0,a_2_3_lattice3(esk1_0,esk2_0)) = esk2_0
    | r1_lattices(esk1_0,esk4_3(esk1_0,esk2_0,a_2_3_lattice3(esk1_0,esk2_0)),esk2_0)
    | ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_25]),c_0_15]),c_0_21])]),c_0_16])).

cnf(c_0_63,plain,
    ( r3_lattices(X1,X2,esk12_3(X3,X1,X2))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,a_2_4_lattice3(X1,X2))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( k16_lattice3(esk1_0,X1) = esk2_0
    | r2_hidden(esk3_3(esk1_0,esk2_0,X1),X1)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_14]),c_0_15]),c_0_33]),c_0_21])]),c_0_16])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk2_0,a_2_4_lattice3(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_35]),c_0_14]),c_0_15]),c_0_33]),c_0_21])]),c_0_16])).

cnf(c_0_66,plain,
    ( X1 = esk12_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_4_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_67,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,esk4_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_68,negated_conjecture,
    ( k15_lattice3(esk1_0,a_2_3_lattice3(esk1_0,esk2_0)) = esk2_0
    | r1_lattices(esk1_0,esk4_3(esk1_0,esk2_0,a_2_3_lattice3(esk1_0,esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_30]),c_0_15]),c_0_21])]),c_0_16])).

cnf(c_0_69,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_70,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk12_3(X1,esk1_0,esk2_0))
    | ~ r2_hidden(X1,a_2_4_lattice3(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_14]),c_0_15]),c_0_33]),c_0_21])]),c_0_16])).

cnf(c_0_71,negated_conjecture,
    ( k16_lattice3(esk1_0,a_2_4_lattice3(esk1_0,esk2_0)) = esk2_0
    | r2_hidden(esk3_3(esk1_0,esk2_0,a_2_4_lattice3(esk1_0,esk2_0)),a_2_4_lattice3(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( esk12_3(X1,esk1_0,esk2_0) = X1
    | ~ r2_hidden(X1,a_2_4_lattice3(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_14]),c_0_15]),c_0_33]),c_0_21])]),c_0_16])).

cnf(c_0_73,negated_conjecture,
    ( k15_lattice3(esk1_0,a_2_3_lattice3(esk1_0,esk2_0)) = esk2_0
    | r4_lattice3(esk1_0,esk2_0,a_2_3_lattice3(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_74,negated_conjecture,
    ( r3_lattice3(esk1_0,esk2_0,X1)
    | m1_subset_1(esk3_3(esk1_0,esk2_0,X1),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_75,negated_conjecture,
    ( k16_lattice3(esk1_0,a_2_4_lattice3(esk1_0,esk2_0)) = esk2_0
    | r3_lattices(esk1_0,esk2_0,esk12_3(esk3_3(esk1_0,esk2_0,a_2_4_lattice3(esk1_0,esk2_0)),esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( esk12_3(esk3_3(esk1_0,esk2_0,a_2_4_lattice3(esk1_0,esk2_0)),esk1_0,esk2_0) = esk3_3(esk1_0,esk2_0,a_2_4_lattice3(esk1_0,esk2_0))
    | k16_lattice3(esk1_0,a_2_4_lattice3(esk1_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( esk2_0 != k15_lattice3(esk1_0,a_2_3_lattice3(esk1_0,esk2_0))
    | esk2_0 != k16_lattice3(esk1_0,a_2_4_lattice3(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_78,negated_conjecture,
    ( k15_lattice3(esk1_0,a_2_3_lattice3(esk1_0,esk2_0)) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_73]),c_0_38]),c_0_14]),c_0_15]),c_0_33]),c_0_21])]),c_0_16])).

cnf(c_0_79,negated_conjecture,
    ( k16_lattice3(esk1_0,X1) = esk2_0
    | m1_subset_1(esk3_3(esk1_0,esk2_0,X1),u1_struct_0(esk1_0))
    | ~ r2_hidden(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_74]),c_0_14]),c_0_15]),c_0_33]),c_0_21])]),c_0_16])).

cnf(c_0_80,negated_conjecture,
    ( k16_lattice3(esk1_0,a_2_4_lattice3(esk1_0,esk2_0)) = esk2_0
    | r3_lattices(esk1_0,esk2_0,esk3_3(esk1_0,esk2_0,a_2_4_lattice3(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( k16_lattice3(esk1_0,a_2_4_lattice3(esk1_0,esk2_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_78])])).

cnf(c_0_82,negated_conjecture,
    ( k16_lattice3(esk1_0,a_2_4_lattice3(esk1_0,esk2_0)) = esk2_0
    | m1_subset_1(esk3_3(esk1_0,esk2_0,a_2_4_lattice3(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_65])).

cnf(c_0_83,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk3_3(esk1_0,esk2_0,a_2_4_lattice3(esk1_0,esk2_0))) ),
    inference(sr,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk3_3(esk1_0,esk2_0,a_2_4_lattice3(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[c_0_82,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,esk3_3(esk1_0,esk2_0,a_2_4_lattice3(esk1_0,esk2_0)))
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_83]),c_0_84]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_86,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,esk3_3(esk1_0,esk2_0,a_2_4_lattice3(esk1_0,esk2_0)))
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_20]),c_0_15]),c_0_21])]),c_0_16])).

cnf(c_0_87,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,esk3_3(esk1_0,esk2_0,a_2_4_lattice3(esk1_0,esk2_0)))
    | ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_25]),c_0_15]),c_0_21])]),c_0_16])).

cnf(c_0_88,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk3_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_89,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,esk3_3(esk1_0,esk2_0,a_2_4_lattice3(esk1_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_30]),c_0_15]),c_0_21])]),c_0_16])).

cnf(c_0_90,negated_conjecture,
    ( r3_lattice3(esk1_0,esk2_0,a_2_4_lattice3(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_90]),c_0_65]),c_0_14]),c_0_15]),c_0_33]),c_0_21])]),c_0_81]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
