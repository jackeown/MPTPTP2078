%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1207+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:03 EST 2020

% Result     : Theorem 5.17s
% Output     : CNFRefutation 5.17s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 176 expanded)
%              Number of clauses        :   23 (  58 expanded)
%              Number of leaves         :    7 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :  215 ( 962 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r3_lattices(X1,k5_lattices(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattices)).

fof(d16_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v13_lattices(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( X2 = k5_lattices(X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( k2_lattices(X1,X2,X3) = X2
                    & k2_lattices(X1,X3,X2) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

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

fof(t21_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k2_lattices(X1,X2,X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

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

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v13_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => r3_lattices(X1,k5_lattices(X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t41_lattices])).

fof(c_0_8,plain,(
    ! [X29,X30,X31] :
      ( ( k2_lattices(X29,X30,X31) = X30
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | X30 != k5_lattices(X29)
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ v13_lattices(X29)
        | v2_struct_0(X29)
        | ~ l1_lattices(X29) )
      & ( k2_lattices(X29,X31,X30) = X30
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | X30 != k5_lattices(X29)
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ v13_lattices(X29)
        | v2_struct_0(X29)
        | ~ l1_lattices(X29) )
      & ( m1_subset_1(esk3_2(X29,X30),u1_struct_0(X29))
        | X30 = k5_lattices(X29)
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ v13_lattices(X29)
        | v2_struct_0(X29)
        | ~ l1_lattices(X29) )
      & ( k2_lattices(X29,X30,esk3_2(X29,X30)) != X30
        | k2_lattices(X29,esk3_2(X29,X30),X30) != X30
        | X30 = k5_lattices(X29)
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | ~ v13_lattices(X29)
        | v2_struct_0(X29)
        | ~ l1_lattices(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

fof(c_0_9,plain,(
    ! [X33] :
      ( v2_struct_0(X33)
      | ~ l1_lattices(X33)
      | m1_subset_1(k5_lattices(X33),u1_struct_0(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_10,plain,(
    ! [X201] :
      ( ( l1_lattices(X201)
        | ~ l3_lattices(X201) )
      & ( l2_lattices(X201)
        | ~ l3_lattices(X201) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v13_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ~ r3_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

cnf(c_0_12,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | X2 != k5_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X182] :
      ( ( ~ v2_struct_0(X182)
        | v2_struct_0(X182)
        | ~ v10_lattices(X182)
        | ~ l3_lattices(X182) )
      & ( v4_lattices(X182)
        | v2_struct_0(X182)
        | ~ v10_lattices(X182)
        | ~ l3_lattices(X182) )
      & ( v5_lattices(X182)
        | v2_struct_0(X182)
        | ~ v10_lattices(X182)
        | ~ l3_lattices(X182) )
      & ( v6_lattices(X182)
        | v2_struct_0(X182)
        | ~ v10_lattices(X182)
        | ~ l3_lattices(X182) )
      & ( v7_lattices(X182)
        | v2_struct_0(X182)
        | ~ v10_lattices(X182)
        | ~ l3_lattices(X182) )
      & ( v8_lattices(X182)
        | v2_struct_0(X182)
        | ~ v10_lattices(X182)
        | ~ l3_lattices(X182) )
      & ( v9_lattices(X182)
        | v2_struct_0(X182)
        | ~ v10_lattices(X182)
        | ~ l3_lattices(X182) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_17,plain,(
    ! [X220,X221,X222] :
      ( ( ~ r1_lattices(X220,X221,X222)
        | k2_lattices(X220,X221,X222) = X221
        | ~ m1_subset_1(X222,u1_struct_0(X220))
        | ~ m1_subset_1(X221,u1_struct_0(X220))
        | v2_struct_0(X220)
        | ~ v8_lattices(X220)
        | ~ v9_lattices(X220)
        | ~ l3_lattices(X220) )
      & ( k2_lattices(X220,X221,X222) != X221
        | r1_lattices(X220,X221,X222)
        | ~ m1_subset_1(X222,u1_struct_0(X220))
        | ~ m1_subset_1(X221,u1_struct_0(X220))
        | v2_struct_0(X220)
        | ~ v8_lattices(X220)
        | ~ v9_lattices(X220)
        | ~ l3_lattices(X220) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_18,plain,
    ( k2_lattices(X1,k5_lattices(X1),X2) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v13_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( l1_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_26,plain,(
    ! [X23,X24,X25] :
      ( ( ~ r3_lattices(X23,X24,X25)
        | r1_lattices(X23,X24,X25)
        | v2_struct_0(X23)
        | ~ v6_lattices(X23)
        | ~ v8_lattices(X23)
        | ~ v9_lattices(X23)
        | ~ l3_lattices(X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23)) )
      & ( ~ r1_lattices(X23,X24,X25)
        | r3_lattices(X23,X24,X25)
        | v2_struct_0(X23)
        | ~ v6_lattices(X23)
        | ~ v8_lattices(X23)
        | ~ v9_lattices(X23)
        | ~ l3_lattices(X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_27,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X3) != X2
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( k2_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) = k5_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_15]),c_0_24])]),c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_15]),c_0_24])]),c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_21]),c_0_22])).

cnf(c_0_32,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( r1_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_15]),c_0_19]),c_0_31])]),c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_15]),c_0_24])]),c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( ~ r3_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_29]),c_0_30]),c_0_35]),c_0_15]),c_0_19]),c_0_31])]),c_0_36]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
