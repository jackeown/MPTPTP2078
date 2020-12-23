%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:59 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  131 (97885 expanded)
%              Number of clauses        :  114 (35050 expanded)
%              Number of leaves         :    8 (24095 expanded)
%              Depth                    :   40
%              Number of atoms          :  804 (719231 expanded)
%              Number of equality atoms :  109 (72181 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   50 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d18_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v4_lattice3(X1)
      <=> ! [X2] :
          ? [X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
            & r4_lattice3(X1,X3,X2)
            & ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r4_lattice3(X1,X4,X2)
                 => r1_lattices(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_lattice3)).

fof(t37_lattice3,conjecture,(
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

fof(c_0_8,plain,(
    ! [X27,X28,X29,X31,X32] :
      ( ( m1_subset_1(esk6_3(X27,X28,X29),u1_struct_0(X28))
        | ~ r2_hidden(X27,a_2_2_lattice3(X28,X29))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28) )
      & ( X27 = esk6_3(X27,X28,X29)
        | ~ r2_hidden(X27,a_2_2_lattice3(X28,X29))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ v4_lattice3(X28)
        | ~ l3_lattices(X28) )
      & ( r4_lattice3(X28,esk6_3(X27,X28,X29),X29)
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

cnf(c_0_9,plain,
    ( r2_hidden(X3,a_2_2_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r4_lattice3(X2,X1,X4)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_10,plain,(
    ! [X15,X16,X18,X20] :
      ( ( m1_subset_1(esk2_2(X15,X16),u1_struct_0(X15))
        | ~ v4_lattice3(X15)
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( r4_lattice3(X15,esk2_2(X15,X16),X16)
        | ~ v4_lattice3(X15)
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ r4_lattice3(X15,X18,X16)
        | r1_lattices(X15,esk2_2(X15,X16),X18)
        | ~ v4_lattice3(X15)
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( m1_subset_1(esk4_2(X15,X20),u1_struct_0(X15))
        | ~ m1_subset_1(X20,u1_struct_0(X15))
        | ~ r4_lattice3(X15,X20,esk3_1(X15))
        | v4_lattice3(X15)
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( r4_lattice3(X15,esk4_2(X15,X20),esk3_1(X15))
        | ~ m1_subset_1(X20,u1_struct_0(X15))
        | ~ r4_lattice3(X15,X20,esk3_1(X15))
        | v4_lattice3(X15)
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( ~ r1_lattices(X15,X20,esk4_2(X15,X20))
        | ~ m1_subset_1(X20,u1_struct_0(X15))
        | ~ r4_lattice3(X15,X20,esk3_1(X15))
        | v4_lattice3(X15)
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_lattice3])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ v4_lattice3(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( r4_lattice3(X1,esk2_2(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2] : k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_2_lattice3(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t37_lattice3])).

fof(c_0_15,plain,(
    ! [X22,X23,X24,X25] :
      ( ( r4_lattice3(X22,X24,X23)
        | X24 != k15_lattice3(X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v10_lattices(X22)
        | ~ v4_lattice3(X22)
        | ~ l3_lattices(X22)
        | v2_struct_0(X22)
        | ~ l3_lattices(X22) )
      & ( ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r4_lattice3(X22,X25,X23)
        | r1_lattices(X22,X24,X25)
        | X24 != k15_lattice3(X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v10_lattices(X22)
        | ~ v4_lattice3(X22)
        | ~ l3_lattices(X22)
        | v2_struct_0(X22)
        | ~ l3_lattices(X22) )
      & ( m1_subset_1(esk5_3(X22,X23,X24),u1_struct_0(X22))
        | ~ r4_lattice3(X22,X24,X23)
        | X24 = k15_lattice3(X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v10_lattices(X22)
        | ~ v4_lattice3(X22)
        | ~ l3_lattices(X22)
        | v2_struct_0(X22)
        | ~ l3_lattices(X22) )
      & ( r4_lattice3(X22,esk5_3(X22,X23,X24),X23)
        | ~ r4_lattice3(X22,X24,X23)
        | X24 = k15_lattice3(X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v10_lattices(X22)
        | ~ v4_lattice3(X22)
        | ~ l3_lattices(X22)
        | v2_struct_0(X22)
        | ~ l3_lattices(X22) )
      & ( ~ r1_lattices(X22,X24,esk5_3(X22,X23,X24))
        | ~ r4_lattice3(X22,X24,X23)
        | X24 = k15_lattice3(X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ v10_lattices(X22)
        | ~ v4_lattice3(X22)
        | ~ l3_lattices(X22)
        | v2_struct_0(X22)
        | ~ l3_lattices(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

cnf(c_0_16,plain,
    ( X1 = esk6_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_2(X1,X2),a_2_2_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    & v10_lattices(esk8_0)
    & v4_lattice3(esk8_0)
    & l3_lattices(esk8_0)
    & k15_lattice3(esk8_0,esk9_0) != k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_19,plain,
    ( r4_lattice3(X1,esk5_3(X1,X2,X3),X2)
    | X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r4_lattice3(X1,esk6_3(X2,X1,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_2_lattice3(X1,X3))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( esk6_3(esk2_2(X1,X2),X1,X2) = esk2_2(X1,X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v4_lattice3(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v10_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( l3_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | r4_lattice3(X1,esk5_3(X1,X2,X3),X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( X3 = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r4_lattice3(X1,esk6_3(esk2_2(X1,X2),X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( esk6_3(esk2_2(esk8_0,X1),esk8_0,X1) = esk2_2(esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_31,plain,
    ( X1 = k15_lattice3(X2,X3)
    | r2_hidden(esk5_3(X2,X3,X1),a_2_2_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ v4_lattice3(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_27]),c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r4_lattice3(esk8_0,esk2_2(esk8_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk2_2(esk8_0,X1),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_23]),c_0_25])]),c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( esk2_2(esk8_0,X1) = k15_lattice3(esk8_0,X1)
    | r2_hidden(esk5_3(esk8_0,X1,esk2_2(esk8_0,X1)),a_2_2_lattice3(esk8_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_23]),c_0_33]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( esk2_2(esk8_0,X1) = k15_lattice3(esk8_0,X1)
    | r4_lattice3(esk8_0,esk6_3(esk5_3(esk8_0,X1,esk2_2(esk8_0,X1)),esk8_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_34]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( esk6_3(esk5_3(esk8_0,X1,esk2_2(esk8_0,X1)),esk8_0,X1) = esk5_3(esk8_0,X1,esk2_2(esk8_0,X1))
    | esk2_2(esk8_0,X1) = k15_lattice3(esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_34]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

fof(c_0_37,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r3_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ r2_hidden(X12,X11)
        | r1_lattices(X9,X10,X12)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk1_3(X9,X10,X13),u1_struct_0(X9))
        | r3_lattice3(X9,X10,X13)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( r2_hidden(esk1_3(X9,X10,X13),X13)
        | r3_lattice3(X9,X10,X13)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( ~ r1_lattices(X9,X10,esk1_3(X9,X10,X13))
        | r3_lattice3(X9,X10,X13)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

cnf(c_0_38,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk5_3(X1,X3,X2))
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,plain,
    ( r1_lattices(X2,esk2_2(X2,X3),X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r4_lattice3(X2,X1,X3)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( esk2_2(esk8_0,X1) = k15_lattice3(esk8_0,X1)
    | r4_lattice3(esk8_0,esk5_3(esk8_0,X1,esk2_2(esk8_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( esk2_2(esk8_0,X1) = k15_lattice3(esk8_0,X1)
    | m1_subset_1(esk5_3(esk8_0,X1,esk2_2(esk8_0,X1)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_32]),c_0_23]),c_0_33]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_43,plain,(
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
      & ( m1_subset_1(esk7_3(X33,X34,X37),u1_struct_0(X33))
        | ~ r3_lattice3(X33,X34,X37)
        | X34 = k16_lattice3(X33,X37)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ v4_lattice3(X33)
        | ~ l3_lattices(X33) )
      & ( r3_lattice3(X33,esk7_3(X33,X34,X37),X37)
        | ~ r3_lattice3(X33,X34,X37)
        | X34 = k16_lattice3(X33,X37)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ v4_lattice3(X33)
        | ~ l3_lattices(X33) )
      & ( ~ r3_lattices(X33,esk7_3(X33,X34,X37),X34)
        | ~ r3_lattice3(X33,X34,X37)
        | X34 = k16_lattice3(X33,X37)
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ v4_lattice3(X33)
        | ~ l3_lattices(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( X2 = k15_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,esk5_3(X1,X3,X2)) ),
    inference(cn,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( esk2_2(esk8_0,X1) = k15_lattice3(esk8_0,X1)
    | r1_lattices(esk8_0,esk2_2(esk8_0,X1),esk5_3(esk8_0,X1,esk2_2(esk8_0,X1))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_23]),c_0_25])]),c_0_26]),c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_3(esk8_0,esk2_2(esk8_0,X1),X2),X2)
    | r3_lattice3(esk8_0,esk2_2(esk8_0,X1),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_33]),c_0_25])]),c_0_26])).

cnf(c_0_48,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( r3_lattice3(X1,esk7_3(X1,X2,X3),X3)
    | X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r3_lattice3(esk8_0,esk2_2(esk8_0,X1),X2)
    | m1_subset_1(esk1_3(esk8_0,esk2_2(esk8_0,X1),X2),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_33]),c_0_25])]),c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( esk2_2(esk8_0,X1) = k15_lattice3(esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_32]),c_0_23]),c_0_33]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( esk6_3(esk1_3(esk8_0,esk2_2(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3) = esk1_3(esk8_0,esk2_2(esk8_0,X1),a_2_2_lattice3(X2,X3))
    | r3_lattice3(esk8_0,esk2_2(esk8_0,X1),a_2_2_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_47])).

cnf(c_0_54,plain,
    ( X1 = k16_lattice3(X2,X3)
    | r1_lattices(X2,esk7_3(X2,X1,X3),X4)
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(X4,X3)
    | ~ r3_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),X2)
    | m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),X2),u1_struct_0(esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk8_0,X1),u1_struct_0(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3) = esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3))
    | r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_52]),c_0_52]),c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,X2)
    | r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),X2),X3)
    | m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),X2),u1_struct_0(esk8_0))
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_23]),c_0_56]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk2_2(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_32]),c_0_23]),c_0_33]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_60,negated_conjecture,
    ( esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3) = esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3))
    | k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))
    | r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X4)
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(X4,a_2_2_lattice3(X2,X3))
    | ~ m1_subset_1(X4,u1_struct_0(esk8_0))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_57]),c_0_23]),c_0_56]),c_0_24]),c_0_25])]),c_0_26])).

fof(c_0_61,plain,(
    ! [X6,X7,X8] :
      ( ( ~ r3_lattices(X6,X7,X8)
        | r1_lattices(X6,X7,X8)
        | v2_struct_0(X6)
        | ~ v6_lattices(X6)
        | ~ v8_lattices(X6)
        | ~ v9_lattices(X6)
        | ~ l3_lattices(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ m1_subset_1(X8,u1_struct_0(X6)) )
      & ( ~ r1_lattices(X6,X7,X8)
        | r3_lattices(X6,X7,X8)
        | v2_struct_0(X6)
        | ~ v6_lattices(X6)
        | ~ v8_lattices(X6)
        | ~ v9_lattices(X6)
        | ~ l3_lattices(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ m1_subset_1(X8,u1_struct_0(X6)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_62,negated_conjecture,
    ( k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,X2)
    | r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),X2),k15_lattice3(esk8_0,X3))
    | m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),X2),u1_struct_0(esk8_0))
    | ~ r2_hidden(k15_lattice3(esk8_0,X3),X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)) ),
    inference(rw,[status(thm)],[c_0_59,c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( esk2_2(esk8_0,X1) = k16_lattice3(esk8_0,X2)
    | m1_subset_1(esk1_3(esk8_0,esk2_2(esk8_0,X1),X2),u1_struct_0(esk8_0))
    | m1_subset_1(esk7_3(esk8_0,esk2_2(esk8_0,X1),X2),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_23]),c_0_33]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_65,negated_conjecture,
    ( esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3) = esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3))
    | k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))
    | r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),k15_lattice3(esk8_0,X4))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(k15_lattice3(esk8_0,X4),a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3) = esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3))
    | k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))
    | m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_57]),c_0_23]),c_0_56]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_67,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))
    | r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))
    | m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,X2)
    | m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),X2),u1_struct_0(esk8_0))
    | m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),X2),u1_struct_0(esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_52]),c_0_52]),c_0_52])).

fof(c_0_70,plain,(
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

cnf(c_0_71,negated_conjecture,
    ( esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),esk8_0,X2) = esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2))
    | k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))
    | r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_63]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_72,negated_conjecture,
    ( esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),esk8_0,X2) = esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2))
    | k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))
    | m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_73,negated_conjecture,
    ( k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))
    | r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))
    | m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),u1_struct_0(esk8_0))
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_56]),c_0_25])]),c_0_26]),c_0_69])).

cnf(c_0_74,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_75,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_76,negated_conjecture,
    ( esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),esk8_0,X2) = esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2))
    | k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))
    | r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_71]),c_0_56]),c_0_25])]),c_0_26]),c_0_72])).

cnf(c_0_77,plain,
    ( X2 = k16_lattice3(X1,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,esk7_3(X1,X2,X3),X2)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_78,negated_conjecture,
    ( k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))
    | r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))
    | m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),u1_struct_0(esk8_0))
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_79,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_80,negated_conjecture,
    ( r4_lattice3(X1,esk6_3(esk1_3(esk8_0,esk2_2(esk8_0,X2),a_2_2_lattice3(X1,X3)),X1,X3),X3)
    | r3_lattice3(esk8_0,esk2_2(esk8_0,X2),a_2_2_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_47])).

cnf(c_0_81,negated_conjecture,
    ( r3_lattice3(esk8_0,esk2_2(esk8_0,X1),a_2_2_lattice3(X2,X3))
    | m1_subset_1(esk6_3(esk1_3(esk8_0,esk2_2(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_47])).

cnf(c_0_82,negated_conjecture,
    ( esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),esk8_0,X2) = esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2))
    | k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))
    | r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_74]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_83,negated_conjecture,
    ( esk2_2(esk8_0,X1) = k16_lattice3(esk8_0,X2)
    | m1_subset_1(esk1_3(esk8_0,esk2_2(esk8_0,X1),X2),u1_struct_0(esk8_0))
    | ~ r3_lattices(esk8_0,esk7_3(esk8_0,esk2_2(esk8_0,X1),X2),esk2_2(esk8_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_51]),c_0_23]),c_0_33]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_84,negated_conjecture,
    ( k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))
    | r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))
    | m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),u1_struct_0(esk8_0))
    | ~ v9_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_85,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_86,negated_conjecture,
    ( r4_lattice3(X1,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X2),a_2_2_lattice3(X1,X3)),X1,X3),X3)
    | r3_lattice3(esk8_0,k15_lattice3(esk8_0,X2),a_2_2_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_52]),c_0_52])).

cnf(c_0_87,negated_conjecture,
    ( r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3))
    | m1_subset_1(esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_52]),c_0_52])).

cnf(c_0_88,negated_conjecture,
    ( esk6_3(esk1_3(esk8_0,esk2_2(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3) = esk1_3(esk8_0,esk2_2(esk8_0,X1),a_2_2_lattice3(X2,X3))
    | esk2_2(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r3_lattices(esk8_0,esk7_3(esk8_0,esk2_2(esk8_0,X1),a_2_2_lattice3(X2,X3)),esk2_2(esk8_0,X1))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_53]),c_0_23]),c_0_33]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_89,negated_conjecture,
    ( esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),esk8_0,X2) = esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2))
    | k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))
    | r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))
    | ~ v9_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_79]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_90,negated_conjecture,
    ( r4_lattice3(X1,esk6_3(esk1_3(esk8_0,esk2_2(esk8_0,X2),a_2_2_lattice3(X1,X3)),X1,X3),X3)
    | r1_lattices(esk8_0,esk2_2(esk8_0,X2),X4)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X4,a_2_2_lattice3(X1,X3))
    | ~ m1_subset_1(X4,u1_struct_0(esk8_0))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_80]),c_0_33]),c_0_25])]),c_0_26])).

cnf(c_0_91,negated_conjecture,
    ( k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,X2)
    | m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),X2),u1_struct_0(esk8_0))
    | ~ r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),X2),k15_lattice3(esk8_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_52]),c_0_52]),c_0_52]),c_0_52])).

cnf(c_0_92,negated_conjecture,
    ( k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))
    | r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))
    | m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_93,negated_conjecture,
    ( k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))
    | r4_lattice3(X2,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3),X3)
    | m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_86]),c_0_23]),c_0_56]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_94,negated_conjecture,
    ( k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))
    | m1_subset_1(esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3),u1_struct_0(X2))
    | m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_87]),c_0_23]),c_0_56]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_95,negated_conjecture,
    ( esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3) = esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3))
    | k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),k15_lattice3(esk8_0,X1))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52])).

cnf(c_0_96,negated_conjecture,
    ( esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),esk8_0,X2) = esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2))
    | k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))
    | r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_85]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_97,negated_conjecture,
    ( r4_lattice3(X1,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X2),a_2_2_lattice3(X1,X3)),X1,X3),X3)
    | r1_lattices(esk8_0,k15_lattice3(esk8_0,X2),X4)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r2_hidden(X4,a_2_2_lattice3(X1,X3))
    | ~ m1_subset_1(X4,u1_struct_0(esk8_0))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_52]),c_0_52])).

cnf(c_0_98,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))
    | r4_lattice3(X2,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3),X3)
    | r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X4)
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(X4,a_2_2_lattice3(X2,X3))
    | ~ m1_subset_1(X4,u1_struct_0(esk8_0))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_86]),c_0_23]),c_0_56]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_100,negated_conjecture,
    ( k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))
    | r1_lattices(X2,esk2_2(X2,X3),esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3))
    | m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),u1_struct_0(esk8_0))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_93]),c_0_94])).

cnf(c_0_101,negated_conjecture,
    ( esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),esk8_0,X1) = esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1))
    | k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_102,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | r4_lattice3(X2,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X3),a_2_2_lattice3(X2,X4)),X2,X4),X4)
    | r1_lattices(esk8_0,k15_lattice3(esk8_0,X3),esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),a_2_2_lattice3(X2,X4))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),X2),X2)
    | r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_52]),c_0_52])).

cnf(c_0_104,negated_conjecture,
    ( k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))
    | r4_lattice3(X2,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3),X3)
    | r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),k15_lattice3(esk8_0,X4))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ r2_hidden(k15_lattice3(esk8_0,X4),a_2_2_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(spm,[status(thm)],[c_0_99,c_0_56])).

cnf(c_0_105,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk1_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_106,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | r1_lattices(esk8_0,k15_lattice3(esk8_0,X1),esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)))
    | m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_52]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_107,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X2),a_2_2_lattice3(esk8_0,X1)),esk8_0,X1),X1)
    | r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1))
    | r1_lattices(esk8_0,k15_lattice3(esk8_0,X2),esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_108,negated_conjecture,
    ( k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))
    | r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),esk8_0,X2),X2)
    | r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_63]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_109,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1))
    | m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_56]),c_0_25])]),c_0_26])).

cnf(c_0_110,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),esk8_0,X1),X1)
    | r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_107]),c_0_56]),c_0_25])]),c_0_26])).

cnf(c_0_111,negated_conjecture,
    ( k15_lattice3(esk8_0,X1) = k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))
    | r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),esk8_0,X2),X2)
    | r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))
    | ~ m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),u1_struct_0(esk8_0))
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_108]),c_0_56]),c_0_25])]),c_0_26])).

cnf(c_0_112,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_109]),c_0_23]),c_0_56]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_113,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),esk8_0,X1),X1)
    | ~ r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_110]),c_0_23]),c_0_56]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_114,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),esk8_0,X1),X1)
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_113])).

cnf(c_0_115,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),esk8_0,X1),X1)
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_74]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_116,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),esk8_0,X1),X1)
    | ~ v9_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_79]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_117,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),esk8_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_85]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_118,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | r4_lattice3(esk8_0,esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_117,c_0_101])).

cnf(c_0_119,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | r1_lattices(esk8_0,k15_lattice3(esk8_0,X1),esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_118]),c_0_52]),c_0_23]),c_0_25])]),c_0_26]),c_0_98])).

cnf(c_0_120,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_119]),c_0_56]),c_0_25])]),c_0_26])).

cnf(c_0_121,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),X2)
    | ~ r2_hidden(X2,a_2_2_lattice3(esk8_0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_120]),c_0_23]),c_0_56]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_122,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X2))
    | ~ r2_hidden(k15_lattice3(esk8_0,X2),a_2_2_lattice3(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_121,c_0_56])).

cnf(c_0_123,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_122,c_0_63])).

cnf(c_0_124,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | ~ r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_120]),c_0_23]),c_0_56]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_125,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0)
    | ~ v6_lattices(esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_123]),c_0_56]),c_0_25])]),c_0_26]),c_0_112]),c_0_124])).

cnf(c_0_126,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | ~ v9_lattices(esk8_0)
    | ~ v8_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_74]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_127,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1)
    | ~ v9_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_79]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_128,negated_conjecture,
    ( k15_lattice3(esk8_0,esk9_0) != k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_129,negated_conjecture,
    ( k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1)) = k15_lattice3(esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_85]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_130,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_129])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:49:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.19/0.44  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.030 s
% 0.19/0.44  # Presaturation interreduction done
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(fraenkel_a_2_2_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_2_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r4_lattice3(X2,X4,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 0.19/0.44  fof(d18_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v4_lattice3(X1)<=>![X2]:?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r4_lattice3(X1,X3,X2))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_lattice3)).
% 0.19/0.44  fof(t37_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 0.19/0.44  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 0.19/0.44  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 0.19/0.44  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 0.19/0.44  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.19/0.44  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.19/0.44  fof(c_0_8, plain, ![X27, X28, X29, X31, X32]:((((m1_subset_1(esk6_3(X27,X28,X29),u1_struct_0(X28))|~r2_hidden(X27,a_2_2_lattice3(X28,X29))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28)))&(X27=esk6_3(X27,X28,X29)|~r2_hidden(X27,a_2_2_lattice3(X28,X29))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28))))&(r4_lattice3(X28,esk6_3(X27,X28,X29),X29)|~r2_hidden(X27,a_2_2_lattice3(X28,X29))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28))))&(~m1_subset_1(X32,u1_struct_0(X28))|X27!=X32|~r4_lattice3(X28,X32,X31)|r2_hidden(X27,a_2_2_lattice3(X28,X31))|(v2_struct_0(X28)|~v10_lattices(X28)|~v4_lattice3(X28)|~l3_lattices(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_lattice3])])])])])])])).
% 0.19/0.44  cnf(c_0_9, plain, (r2_hidden(X3,a_2_2_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r4_lattice3(X2,X1,X4)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.44  fof(c_0_10, plain, ![X15, X16, X18, X20]:((((m1_subset_1(esk2_2(X15,X16),u1_struct_0(X15))|~v4_lattice3(X15)|(v2_struct_0(X15)|~l3_lattices(X15)))&(r4_lattice3(X15,esk2_2(X15,X16),X16)|~v4_lattice3(X15)|(v2_struct_0(X15)|~l3_lattices(X15))))&(~m1_subset_1(X18,u1_struct_0(X15))|(~r4_lattice3(X15,X18,X16)|r1_lattices(X15,esk2_2(X15,X16),X18))|~v4_lattice3(X15)|(v2_struct_0(X15)|~l3_lattices(X15))))&((m1_subset_1(esk4_2(X15,X20),u1_struct_0(X15))|(~m1_subset_1(X20,u1_struct_0(X15))|~r4_lattice3(X15,X20,esk3_1(X15)))|v4_lattice3(X15)|(v2_struct_0(X15)|~l3_lattices(X15)))&((r4_lattice3(X15,esk4_2(X15,X20),esk3_1(X15))|(~m1_subset_1(X20,u1_struct_0(X15))|~r4_lattice3(X15,X20,esk3_1(X15)))|v4_lattice3(X15)|(v2_struct_0(X15)|~l3_lattices(X15)))&(~r1_lattices(X15,X20,esk4_2(X15,X20))|(~m1_subset_1(X20,u1_struct_0(X15))|~r4_lattice3(X15,X20,esk3_1(X15)))|v4_lattice3(X15)|(v2_struct_0(X15)|~l3_lattices(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_lattice3])])])])])])).
% 0.19/0.44  cnf(c_0_11, plain, (r2_hidden(X1,a_2_2_lattice3(X2,X3))|v2_struct_0(X2)|~r4_lattice3(X2,X1,X3)|~v4_lattice3(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_9])).
% 0.19/0.44  cnf(c_0_12, plain, (r4_lattice3(X1,esk2_2(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.44  cnf(c_0_13, plain, (m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))|v2_struct_0(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.44  fof(c_0_14, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:k15_lattice3(X1,X2)=k16_lattice3(X1,a_2_2_lattice3(X1,X2)))), inference(assume_negation,[status(cth)],[t37_lattice3])).
% 0.19/0.44  fof(c_0_15, plain, ![X22, X23, X24, X25]:(((r4_lattice3(X22,X24,X23)|X24!=k15_lattice3(X22,X23)|~m1_subset_1(X24,u1_struct_0(X22))|(v2_struct_0(X22)|~v10_lattices(X22)|~v4_lattice3(X22)|~l3_lattices(X22))|(v2_struct_0(X22)|~l3_lattices(X22)))&(~m1_subset_1(X25,u1_struct_0(X22))|(~r4_lattice3(X22,X25,X23)|r1_lattices(X22,X24,X25))|X24!=k15_lattice3(X22,X23)|~m1_subset_1(X24,u1_struct_0(X22))|(v2_struct_0(X22)|~v10_lattices(X22)|~v4_lattice3(X22)|~l3_lattices(X22))|(v2_struct_0(X22)|~l3_lattices(X22))))&((m1_subset_1(esk5_3(X22,X23,X24),u1_struct_0(X22))|~r4_lattice3(X22,X24,X23)|X24=k15_lattice3(X22,X23)|~m1_subset_1(X24,u1_struct_0(X22))|(v2_struct_0(X22)|~v10_lattices(X22)|~v4_lattice3(X22)|~l3_lattices(X22))|(v2_struct_0(X22)|~l3_lattices(X22)))&((r4_lattice3(X22,esk5_3(X22,X23,X24),X23)|~r4_lattice3(X22,X24,X23)|X24=k15_lattice3(X22,X23)|~m1_subset_1(X24,u1_struct_0(X22))|(v2_struct_0(X22)|~v10_lattices(X22)|~v4_lattice3(X22)|~l3_lattices(X22))|(v2_struct_0(X22)|~l3_lattices(X22)))&(~r1_lattices(X22,X24,esk5_3(X22,X23,X24))|~r4_lattice3(X22,X24,X23)|X24=k15_lattice3(X22,X23)|~m1_subset_1(X24,u1_struct_0(X22))|(v2_struct_0(X22)|~v10_lattices(X22)|~v4_lattice3(X22)|~l3_lattices(X22))|(v2_struct_0(X22)|~l3_lattices(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.19/0.44  cnf(c_0_16, plain, (X1=esk6_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.44  cnf(c_0_17, plain, (r2_hidden(esk2_2(X1,X2),a_2_2_lattice3(X1,X2))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 0.19/0.44  fof(c_0_18, negated_conjecture, ((((~v2_struct_0(esk8_0)&v10_lattices(esk8_0))&v4_lattice3(esk8_0))&l3_lattices(esk8_0))&k15_lattice3(esk8_0,esk9_0)!=k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,esk9_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.19/0.44  cnf(c_0_19, plain, (r4_lattice3(X1,esk5_3(X1,X2,X3),X2)|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.44  cnf(c_0_20, plain, (m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))|X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|v2_struct_0(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.44  cnf(c_0_21, plain, (r4_lattice3(X1,esk6_3(X2,X1,X3),X3)|v2_struct_0(X1)|~r2_hidden(X2,a_2_2_lattice3(X1,X3))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.44  cnf(c_0_22, plain, (esk6_3(esk2_2(X1,X2),X1,X2)=esk2_2(X1,X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.44  cnf(c_0_23, negated_conjecture, (v4_lattice3(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_24, negated_conjecture, (v10_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_25, negated_conjecture, (l3_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_27, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|r4_lattice3(X1,esk5_3(X1,X2,X3),X2)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_28, plain, (X3=k15_lattice3(X1,X2)|v2_struct_0(X1)|m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_20])).
% 0.19/0.44  cnf(c_0_29, plain, (r4_lattice3(X1,esk6_3(esk2_2(X1,X2),X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_21, c_0_17])).
% 0.19/0.44  cnf(c_0_30, negated_conjecture, (esk6_3(esk2_2(esk8_0,X1),esk8_0,X1)=esk2_2(esk8_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_31, plain, (X1=k15_lattice3(X2,X3)|r2_hidden(esk5_3(X2,X3,X1),a_2_2_lattice3(X2,X3))|v2_struct_0(X2)|~r4_lattice3(X2,X1,X3)|~v4_lattice3(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_27]), c_0_28])).
% 0.19/0.44  cnf(c_0_32, negated_conjecture, (r4_lattice3(esk8_0,esk2_2(esk8_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk2_2(esk8_0,X1),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_23]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_34, negated_conjecture, (esk2_2(esk8_0,X1)=k15_lattice3(esk8_0,X1)|r2_hidden(esk5_3(esk8_0,X1,esk2_2(esk8_0,X1)),a_2_2_lattice3(esk8_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_23]), c_0_33]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_35, negated_conjecture, (esk2_2(esk8_0,X1)=k15_lattice3(esk8_0,X1)|r4_lattice3(esk8_0,esk6_3(esk5_3(esk8_0,X1,esk2_2(esk8_0,X1)),esk8_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_34]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_36, negated_conjecture, (esk6_3(esk5_3(esk8_0,X1,esk2_2(esk8_0,X1)),esk8_0,X1)=esk5_3(esk8_0,X1,esk2_2(esk8_0,X1))|esk2_2(esk8_0,X1)=k15_lattice3(esk8_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_34]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  fof(c_0_37, plain, ![X9, X10, X11, X12, X13]:((~r3_lattice3(X9,X10,X11)|(~m1_subset_1(X12,u1_struct_0(X9))|(~r2_hidden(X12,X11)|r1_lattices(X9,X10,X12)))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&((m1_subset_1(esk1_3(X9,X10,X13),u1_struct_0(X9))|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&((r2_hidden(esk1_3(X9,X10,X13),X13)|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&(~r1_lattices(X9,X10,esk1_3(X9,X10,X13))|r3_lattice3(X9,X10,X13)|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.19/0.44  cnf(c_0_38, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk5_3(X1,X3,X2))|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.44  cnf(c_0_39, plain, (r1_lattices(X2,esk2_2(X2,X3),X1)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r4_lattice3(X2,X1,X3)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.44  cnf(c_0_40, negated_conjecture, (esk2_2(esk8_0,X1)=k15_lattice3(esk8_0,X1)|r4_lattice3(esk8_0,esk5_3(esk8_0,X1,esk2_2(esk8_0,X1)),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.44  cnf(c_0_41, negated_conjecture, (esk2_2(esk8_0,X1)=k15_lattice3(esk8_0,X1)|m1_subset_1(esk5_3(esk8_0,X1,esk2_2(esk8_0,X1)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_32]), c_0_23]), c_0_33]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_42, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.44  fof(c_0_43, plain, ![X33, X34, X35, X36, X37]:(((r3_lattice3(X33,X34,X35)|X34!=k16_lattice3(X33,X35)|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v10_lattices(X33)|~v4_lattice3(X33)|~l3_lattices(X33)))&(~m1_subset_1(X36,u1_struct_0(X33))|(~r3_lattice3(X33,X36,X35)|r3_lattices(X33,X36,X34))|X34!=k16_lattice3(X33,X35)|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v10_lattices(X33)|~v4_lattice3(X33)|~l3_lattices(X33))))&((m1_subset_1(esk7_3(X33,X34,X37),u1_struct_0(X33))|~r3_lattice3(X33,X34,X37)|X34=k16_lattice3(X33,X37)|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v10_lattices(X33)|~v4_lattice3(X33)|~l3_lattices(X33)))&((r3_lattice3(X33,esk7_3(X33,X34,X37),X37)|~r3_lattice3(X33,X34,X37)|X34=k16_lattice3(X33,X37)|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v10_lattices(X33)|~v4_lattice3(X33)|~l3_lattices(X33)))&(~r3_lattices(X33,esk7_3(X33,X34,X37),X34)|~r3_lattice3(X33,X34,X37)|X34=k16_lattice3(X33,X37)|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v10_lattices(X33)|~v4_lattice3(X33)|~l3_lattices(X33)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.19/0.44  cnf(c_0_44, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.44  cnf(c_0_45, plain, (X2=k15_lattice3(X1,X3)|v2_struct_0(X1)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~r1_lattices(X1,X2,esk5_3(X1,X3,X2))), inference(cn,[status(thm)],[c_0_38])).
% 0.19/0.44  cnf(c_0_46, negated_conjecture, (esk2_2(esk8_0,X1)=k15_lattice3(esk8_0,X1)|r1_lattices(esk8_0,esk2_2(esk8_0,X1),esk5_3(esk8_0,X1,esk2_2(esk8_0,X1)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_23]), c_0_25])]), c_0_26]), c_0_41])).
% 0.19/0.44  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_3(esk8_0,esk2_2(esk8_0,X1),X2),X2)|r3_lattice3(esk8_0,esk2_2(esk8_0,X1),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_33]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_48, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.44  cnf(c_0_49, plain, (r3_lattice3(X1,esk7_3(X1,X2,X3),X3)|X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.44  cnf(c_0_50, plain, (m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))|X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.44  cnf(c_0_51, negated_conjecture, (r3_lattice3(esk8_0,esk2_2(esk8_0,X1),X2)|m1_subset_1(esk1_3(esk8_0,esk2_2(esk8_0,X1),X2),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_33]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_52, negated_conjecture, (esk2_2(esk8_0,X1)=k15_lattice3(esk8_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_32]), c_0_23]), c_0_33]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_53, negated_conjecture, (esk6_3(esk1_3(esk8_0,esk2_2(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3)=esk1_3(esk8_0,esk2_2(esk8_0,X1),a_2_2_lattice3(X2,X3))|r3_lattice3(esk8_0,esk2_2(esk8_0,X1),a_2_2_lattice3(X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_16, c_0_47])).
% 0.19/0.44  cnf(c_0_54, plain, (X1=k16_lattice3(X2,X3)|r1_lattices(X2,esk7_3(X2,X1,X3),X4)|v2_struct_0(X2)|~v4_lattice3(X2)|~r2_hidden(X4,X3)|~r3_lattice3(X2,X1,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.19/0.44  cnf(c_0_55, negated_conjecture, (r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),X2)|m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),X2),u1_struct_0(esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_52])).
% 0.19/0.44  cnf(c_0_56, negated_conjecture, (m1_subset_1(k15_lattice3(esk8_0,X1),u1_struct_0(esk8_0))), inference(rw,[status(thm)],[c_0_33, c_0_52])).
% 0.19/0.44  cnf(c_0_57, negated_conjecture, (esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3)=esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3))|r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_52]), c_0_52]), c_0_52])).
% 0.19/0.44  cnf(c_0_58, negated_conjecture, (k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,X2)|r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),X2),X3)|m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),X2),u1_struct_0(esk8_0))|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_23]), c_0_56]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_59, negated_conjecture, (r2_hidden(esk2_2(esk8_0,X1),a_2_2_lattice3(esk8_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_32]), c_0_23]), c_0_33]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_60, negated_conjecture, (esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3)=esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3))|k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))|r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X4)|v2_struct_0(X2)|~v4_lattice3(X2)|~r2_hidden(X4,a_2_2_lattice3(X2,X3))|~m1_subset_1(X4,u1_struct_0(esk8_0))|~v10_lattices(X2)|~l3_lattices(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_57]), c_0_23]), c_0_56]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  fof(c_0_61, plain, ![X6, X7, X8]:((~r3_lattices(X6,X7,X8)|r1_lattices(X6,X7,X8)|(v2_struct_0(X6)|~v6_lattices(X6)|~v8_lattices(X6)|~v9_lattices(X6)|~l3_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))&(~r1_lattices(X6,X7,X8)|r3_lattices(X6,X7,X8)|(v2_struct_0(X6)|~v6_lattices(X6)|~v8_lattices(X6)|~v9_lattices(X6)|~l3_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X8,u1_struct_0(X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.19/0.44  cnf(c_0_62, negated_conjecture, (k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,X2)|r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),X2),k15_lattice3(esk8_0,X3))|m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),X2),u1_struct_0(esk8_0))|~r2_hidden(k15_lattice3(esk8_0,X3),X2)), inference(spm,[status(thm)],[c_0_58, c_0_56])).
% 0.19/0.44  cnf(c_0_63, negated_conjecture, (r2_hidden(k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1))), inference(rw,[status(thm)],[c_0_59, c_0_52])).
% 0.19/0.44  cnf(c_0_64, negated_conjecture, (esk2_2(esk8_0,X1)=k16_lattice3(esk8_0,X2)|m1_subset_1(esk1_3(esk8_0,esk2_2(esk8_0,X1),X2),u1_struct_0(esk8_0))|m1_subset_1(esk7_3(esk8_0,esk2_2(esk8_0,X1),X2),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_23]), c_0_33]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_65, negated_conjecture, (esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3)=esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3))|k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))|r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),k15_lattice3(esk8_0,X4))|v2_struct_0(X2)|~v4_lattice3(X2)|~r2_hidden(k15_lattice3(esk8_0,X4),a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_60, c_0_56])).
% 0.19/0.44  cnf(c_0_66, negated_conjecture, (esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3)=esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3))|k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))|m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),u1_struct_0(esk8_0))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_57]), c_0_23]), c_0_56]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_67, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.44  cnf(c_0_68, negated_conjecture, (k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))|r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))|m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.44  cnf(c_0_69, negated_conjecture, (k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,X2)|m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),X2),u1_struct_0(esk8_0))|m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),X2),u1_struct_0(esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_52]), c_0_52]), c_0_52])).
% 0.19/0.44  fof(c_0_70, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.19/0.44  cnf(c_0_71, negated_conjecture, (esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),esk8_0,X2)=esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2))|k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))|r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_63]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_72, negated_conjecture, (esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),esk8_0,X2)=esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2))|k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))|m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_73, negated_conjecture, (k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))|r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))|m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),u1_struct_0(esk8_0))|~v9_lattices(esk8_0)|~v8_lattices(esk8_0)|~v6_lattices(esk8_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_56]), c_0_25])]), c_0_26]), c_0_69])).
% 0.19/0.44  cnf(c_0_74, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.44  cnf(c_0_75, plain, (m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.44  cnf(c_0_76, negated_conjecture, (esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),esk8_0,X2)=esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2))|k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))|r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))|~v9_lattices(esk8_0)|~v8_lattices(esk8_0)|~v6_lattices(esk8_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_71]), c_0_56]), c_0_25])]), c_0_26]), c_0_72])).
% 0.19/0.44  cnf(c_0_77, plain, (X2=k16_lattice3(X1,X3)|v2_struct_0(X1)|~r3_lattices(X1,esk7_3(X1,X2,X3),X2)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.44  cnf(c_0_78, negated_conjecture, (k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))|r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))|m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),u1_struct_0(esk8_0))|~v9_lattices(esk8_0)|~v8_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_79, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.44  cnf(c_0_80, negated_conjecture, (r4_lattice3(X1,esk6_3(esk1_3(esk8_0,esk2_2(esk8_0,X2),a_2_2_lattice3(X1,X3)),X1,X3),X3)|r3_lattice3(esk8_0,esk2_2(esk8_0,X2),a_2_2_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_21, c_0_47])).
% 0.19/0.44  cnf(c_0_81, negated_conjecture, (r3_lattice3(esk8_0,esk2_2(esk8_0,X1),a_2_2_lattice3(X2,X3))|m1_subset_1(esk6_3(esk1_3(esk8_0,esk2_2(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_75, c_0_47])).
% 0.19/0.44  cnf(c_0_82, negated_conjecture, (esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),esk8_0,X2)=esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2))|k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))|r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))|~v9_lattices(esk8_0)|~v8_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_74]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_83, negated_conjecture, (esk2_2(esk8_0,X1)=k16_lattice3(esk8_0,X2)|m1_subset_1(esk1_3(esk8_0,esk2_2(esk8_0,X1),X2),u1_struct_0(esk8_0))|~r3_lattices(esk8_0,esk7_3(esk8_0,esk2_2(esk8_0,X1),X2),esk2_2(esk8_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_51]), c_0_23]), c_0_33]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_84, negated_conjecture, (k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))|r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))|m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),u1_struct_0(esk8_0))|~v9_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_85, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.44  cnf(c_0_86, negated_conjecture, (r4_lattice3(X1,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X2),a_2_2_lattice3(X1,X3)),X1,X3),X3)|r3_lattice3(esk8_0,k15_lattice3(esk8_0,X2),a_2_2_lattice3(X1,X3))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_52]), c_0_52])).
% 0.19/0.44  cnf(c_0_87, negated_conjecture, (r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3))|m1_subset_1(esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_52]), c_0_52])).
% 0.19/0.44  cnf(c_0_88, negated_conjecture, (esk6_3(esk1_3(esk8_0,esk2_2(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3)=esk1_3(esk8_0,esk2_2(esk8_0,X1),a_2_2_lattice3(X2,X3))|esk2_2(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~r3_lattices(esk8_0,esk7_3(esk8_0,esk2_2(esk8_0,X1),a_2_2_lattice3(X2,X3)),esk2_2(esk8_0,X1))|~v10_lattices(X2)|~l3_lattices(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_53]), c_0_23]), c_0_33]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_89, negated_conjecture, (esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),esk8_0,X2)=esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2))|k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))|r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))|~v9_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_79]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_90, negated_conjecture, (r4_lattice3(X1,esk6_3(esk1_3(esk8_0,esk2_2(esk8_0,X2),a_2_2_lattice3(X1,X3)),X1,X3),X3)|r1_lattices(esk8_0,esk2_2(esk8_0,X2),X4)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X4,a_2_2_lattice3(X1,X3))|~m1_subset_1(X4,u1_struct_0(esk8_0))|~v10_lattices(X1)|~l3_lattices(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_80]), c_0_33]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_91, negated_conjecture, (k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,X2)|m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),X2),u1_struct_0(esk8_0))|~r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),X2),k15_lattice3(esk8_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_52]), c_0_52]), c_0_52]), c_0_52])).
% 0.19/0.44  cnf(c_0_92, negated_conjecture, (k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))|r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))|m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_93, negated_conjecture, (k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))|r4_lattice3(X2,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3),X3)|m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),u1_struct_0(esk8_0))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_86]), c_0_23]), c_0_56]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_94, negated_conjecture, (k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))|m1_subset_1(esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3),u1_struct_0(X2))|m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),u1_struct_0(esk8_0))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_87]), c_0_23]), c_0_56]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_95, negated_conjecture, (esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3)=esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3))|k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))|v2_struct_0(X2)|~v4_lattice3(X2)|~r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),k15_lattice3(esk8_0,X1))|~v10_lattices(X2)|~l3_lattices(X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52])).
% 0.19/0.44  cnf(c_0_96, negated_conjecture, (esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),esk8_0,X2)=esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2))|k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))|r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_85]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_97, negated_conjecture, (r4_lattice3(X1,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X2),a_2_2_lattice3(X1,X3)),X1,X3),X3)|r1_lattices(esk8_0,k15_lattice3(esk8_0,X2),X4)|v2_struct_0(X1)|~v4_lattice3(X1)|~r2_hidden(X4,a_2_2_lattice3(X1,X3))|~m1_subset_1(X4,u1_struct_0(esk8_0))|~v10_lattices(X1)|~l3_lattices(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_52]), c_0_52])).
% 0.19/0.44  cnf(c_0_98, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|m1_subset_1(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.19/0.44  cnf(c_0_99, negated_conjecture, (k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))|r4_lattice3(X2,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3),X3)|r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X4)|v2_struct_0(X2)|~v4_lattice3(X2)|~r2_hidden(X4,a_2_2_lattice3(X2,X3))|~m1_subset_1(X4,u1_struct_0(esk8_0))|~v10_lattices(X2)|~l3_lattices(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_86]), c_0_23]), c_0_56]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_100, negated_conjecture, (k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))|r1_lattices(X2,esk2_2(X2,X3),esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3))|m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),u1_struct_0(esk8_0))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_93]), c_0_94])).
% 0.19/0.44  cnf(c_0_101, negated_conjecture, (esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),esk8_0,X1)=esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1))|k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_102, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|r4_lattice3(X2,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X3),a_2_2_lattice3(X2,X4)),X2,X4),X4)|r1_lattices(esk8_0,k15_lattice3(esk8_0,X3),esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)))|v2_struct_0(X2)|~v4_lattice3(X2)|~r2_hidden(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),a_2_2_lattice3(X2,X4))|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.19/0.44  cnf(c_0_103, negated_conjecture, (r2_hidden(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),X2),X2)|r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_52]), c_0_52])).
% 0.19/0.44  cnf(c_0_104, negated_conjecture, (k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(X2,X3))|r4_lattice3(X2,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),X2,X3),X3)|r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(X2,X3)),k15_lattice3(esk8_0,X4))|v2_struct_0(X2)|~v4_lattice3(X2)|~r2_hidden(k15_lattice3(esk8_0,X4),a_2_2_lattice3(X2,X3))|~v10_lattices(X2)|~l3_lattices(X2)), inference(spm,[status(thm)],[c_0_99, c_0_56])).
% 0.19/0.44  cnf(c_0_105, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk1_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.44  cnf(c_0_106, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|r1_lattices(esk8_0,k15_lattice3(esk8_0,X1),esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)))|m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_52]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_107, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X2),a_2_2_lattice3(esk8_0,X1)),esk8_0,X1),X1)|r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1))|r1_lattices(esk8_0,k15_lattice3(esk8_0,X2),esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_108, negated_conjecture, (k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))|r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),esk8_0,X2),X2)|r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_63]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_109, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1))|m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_56]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_110, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),esk8_0,X1),X1)|r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_107]), c_0_56]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_111, negated_conjecture, (k15_lattice3(esk8_0,X1)=k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X2))|r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),esk8_0,X2),X2)|r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),k15_lattice3(esk8_0,X2))|~m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X2)),u1_struct_0(esk8_0))|~v9_lattices(esk8_0)|~v8_lattices(esk8_0)|~v6_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_108]), c_0_56]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_112, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|m1_subset_1(esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_109]), c_0_23]), c_0_56]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_113, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),esk8_0,X1),X1)|~r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_110]), c_0_23]), c_0_56]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_114, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),esk8_0,X1),X1)|~v9_lattices(esk8_0)|~v8_lattices(esk8_0)|~v6_lattices(esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_113])).
% 0.19/0.44  cnf(c_0_115, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),esk8_0,X1),X1)|~v9_lattices(esk8_0)|~v8_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_74]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_116, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),esk8_0,X1),X1)|~v9_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_79]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_117, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|r4_lattice3(esk8_0,esk6_3(esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),esk8_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_85]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_118, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|r4_lattice3(esk8_0,esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),X1)), inference(spm,[status(thm)],[c_0_117, c_0_101])).
% 0.19/0.44  cnf(c_0_119, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|r1_lattices(esk8_0,k15_lattice3(esk8_0,X1),esk1_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_118]), c_0_52]), c_0_23]), c_0_25])]), c_0_26]), c_0_98])).
% 0.19/0.44  cnf(c_0_120, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|r3_lattice3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_119]), c_0_56]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_121, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),X2)|~r2_hidden(X2,a_2_2_lattice3(esk8_0,X1))|~m1_subset_1(X2,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_120]), c_0_23]), c_0_56]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_122, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X2))|~r2_hidden(k15_lattice3(esk8_0,X2),a_2_2_lattice3(esk8_0,X1))), inference(spm,[status(thm)],[c_0_121, c_0_56])).
% 0.19/0.44  cnf(c_0_123, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|r1_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X1))), inference(spm,[status(thm)],[c_0_122, c_0_63])).
% 0.19/0.44  cnf(c_0_124, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|~r3_lattices(esk8_0,esk7_3(esk8_0,k15_lattice3(esk8_0,X1),a_2_2_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_120]), c_0_23]), c_0_56]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_125, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|~v9_lattices(esk8_0)|~v8_lattices(esk8_0)|~v6_lattices(esk8_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_123]), c_0_56]), c_0_25])]), c_0_26]), c_0_112]), c_0_124])).
% 0.19/0.44  cnf(c_0_126, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|~v9_lattices(esk8_0)|~v8_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_74]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_127, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)|~v9_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_79]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_128, negated_conjecture, (k15_lattice3(esk8_0,esk9_0)!=k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_129, negated_conjecture, (k16_lattice3(esk8_0,a_2_2_lattice3(esk8_0,X1))=k15_lattice3(esk8_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_85]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_130, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_129])]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 131
% 0.19/0.44  # Proof object clause steps            : 114
% 0.19/0.44  # Proof object formula steps           : 17
% 0.19/0.44  # Proof object conjectures             : 87
% 0.19/0.44  # Proof object clause conjectures      : 84
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 26
% 0.19/0.44  # Proof object initial formulas used   : 8
% 0.19/0.44  # Proof object generating inferences   : 72
% 0.19/0.44  # Proof object simplifying inferences  : 294
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 8
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 38
% 0.19/0.44  # Removed in clause preprocessing      : 1
% 0.19/0.44  # Initial clauses in saturation        : 37
% 0.19/0.44  # Processed clauses                    : 484
% 0.19/0.44  # ...of these trivial                  : 18
% 0.19/0.44  # ...subsumed                          : 94
% 0.19/0.44  # ...remaining for further processing  : 372
% 0.19/0.44  # Other redundant clauses eliminated   : 5
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 66
% 0.19/0.44  # Backward-rewritten                   : 112
% 0.19/0.44  # Generated clauses                    : 904
% 0.19/0.44  # ...of the previous two non-trivial   : 833
% 0.19/0.44  # Contextual simplify-reflections      : 63
% 0.19/0.44  # Paramodulations                      : 899
% 0.19/0.44  # Factorizations                       : 0
% 0.19/0.44  # Equation resolutions                 : 5
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 152
% 0.19/0.44  #    Positive orientable unit clauses  : 11
% 0.19/0.44  #    Positive unorientable unit clauses: 0
% 0.19/0.44  #    Negative unit clauses             : 1
% 0.19/0.44  #    Non-unit-clauses                  : 140
% 0.19/0.44  # Current number of unprocessed clauses: 358
% 0.19/0.44  # ...number of literals in the above   : 2457
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 215
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 19535
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 1507
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 223
% 0.19/0.44  # Unit Clause-clause subsumption calls : 95
% 0.19/0.44  # Rewrite failures with RHS unbound    : 0
% 0.19/0.44  # BW rewrite match attempts            : 13
% 0.19/0.44  # BW rewrite match successes           : 8
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 52241
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.091 s
% 0.19/0.44  # System time              : 0.007 s
% 0.19/0.44  # Total time               : 0.099 s
% 0.19/0.44  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
