%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1507+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:05 EST 2020

% Result     : Theorem 16.55s
% Output     : CNFRefutation 16.55s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 190 expanded)
%              Number of clauses        :   31 (  61 expanded)
%              Number of leaves         :    8 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :  294 (1270 expanded)
%              Number of equality atoms :   15 ( 117 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_lattice3,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT018+2.ax',cc1_lattices)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT018+2.ax',redefinition_r3_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT018+2.ax',dt_l3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT018+2.ax',t26_lattices)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t41_lattice3])).

fof(c_0_9,plain,(
    ! [X9275,X9276,X9277] :
      ( ( r3_lattices(X9275,X9276,k15_lattice3(X9275,X9277))
        | ~ r2_hidden(X9276,X9277)
        | ~ m1_subset_1(X9276,u1_struct_0(X9275))
        | v2_struct_0(X9275)
        | ~ v10_lattices(X9275)
        | ~ v4_lattice3(X9275)
        | ~ l3_lattices(X9275) )
      & ( r3_lattices(X9275,k16_lattice3(X9275,X9277),X9276)
        | ~ r2_hidden(X9276,X9277)
        | ~ m1_subset_1(X9276,u1_struct_0(X9275))
        | v2_struct_0(X9275)
        | ~ v10_lattices(X9275)
        | ~ v4_lattice3(X9275)
        | ~ l3_lattices(X9275) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_lattice3])])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1043_0)
    & v10_lattices(esk1043_0)
    & v4_lattice3(esk1043_0)
    & l3_lattices(esk1043_0)
    & m1_subset_1(esk1044_0,u1_struct_0(esk1043_0))
    & r2_hidden(esk1044_0,esk1045_0)
    & r4_lattice3(esk1043_0,esk1044_0,esk1045_0)
    & k15_lattice3(esk1043_0,esk1045_0) != esk1044_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_11,plain,
    ( r3_lattices(X1,X2,k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk1044_0,u1_struct_0(esk1043_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v4_lattice3(esk1043_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( l3_lattices(esk1043_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v10_lattices(esk1043_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1043_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X6519] :
      ( ( ~ v2_struct_0(X6519)
        | v2_struct_0(X6519)
        | ~ v10_lattices(X6519)
        | ~ l3_lattices(X6519) )
      & ( v4_lattices(X6519)
        | v2_struct_0(X6519)
        | ~ v10_lattices(X6519)
        | ~ l3_lattices(X6519) )
      & ( v5_lattices(X6519)
        | v2_struct_0(X6519)
        | ~ v10_lattices(X6519)
        | ~ l3_lattices(X6519) )
      & ( v6_lattices(X6519)
        | v2_struct_0(X6519)
        | ~ v10_lattices(X6519)
        | ~ l3_lattices(X6519) )
      & ( v7_lattices(X6519)
        | v2_struct_0(X6519)
        | ~ v10_lattices(X6519)
        | ~ l3_lattices(X6519) )
      & ( v8_lattices(X6519)
        | v2_struct_0(X6519)
        | ~ v10_lattices(X6519)
        | ~ l3_lattices(X6519) )
      & ( v9_lattices(X6519)
        | v2_struct_0(X6519)
        | ~ v10_lattices(X6519)
        | ~ l3_lattices(X6519) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_18,plain,(
    ! [X8971,X8972] :
      ( v2_struct_0(X8971)
      | ~ l3_lattices(X8971)
      | m1_subset_1(k15_lattice3(X8971,X8972),u1_struct_0(X8971)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_19,plain,(
    ! [X8922,X8923,X8924,X8925] :
      ( ( r4_lattice3(X8922,X8924,X8923)
        | X8924 != k15_lattice3(X8922,X8923)
        | ~ m1_subset_1(X8924,u1_struct_0(X8922))
        | v2_struct_0(X8922)
        | ~ v10_lattices(X8922)
        | ~ v4_lattice3(X8922)
        | ~ l3_lattices(X8922)
        | v2_struct_0(X8922)
        | ~ l3_lattices(X8922) )
      & ( ~ m1_subset_1(X8925,u1_struct_0(X8922))
        | ~ r4_lattice3(X8922,X8925,X8923)
        | r1_lattices(X8922,X8924,X8925)
        | X8924 != k15_lattice3(X8922,X8923)
        | ~ m1_subset_1(X8924,u1_struct_0(X8922))
        | v2_struct_0(X8922)
        | ~ v10_lattices(X8922)
        | ~ v4_lattice3(X8922)
        | ~ l3_lattices(X8922)
        | v2_struct_0(X8922)
        | ~ l3_lattices(X8922) )
      & ( m1_subset_1(esk989_3(X8922,X8923,X8924),u1_struct_0(X8922))
        | ~ r4_lattice3(X8922,X8924,X8923)
        | X8924 = k15_lattice3(X8922,X8923)
        | ~ m1_subset_1(X8924,u1_struct_0(X8922))
        | v2_struct_0(X8922)
        | ~ v10_lattices(X8922)
        | ~ v4_lattice3(X8922)
        | ~ l3_lattices(X8922)
        | v2_struct_0(X8922)
        | ~ l3_lattices(X8922) )
      & ( r4_lattice3(X8922,esk989_3(X8922,X8923,X8924),X8923)
        | ~ r4_lattice3(X8922,X8924,X8923)
        | X8924 = k15_lattice3(X8922,X8923)
        | ~ m1_subset_1(X8924,u1_struct_0(X8922))
        | v2_struct_0(X8922)
        | ~ v10_lattices(X8922)
        | ~ v4_lattice3(X8922)
        | ~ l3_lattices(X8922)
        | v2_struct_0(X8922)
        | ~ l3_lattices(X8922) )
      & ( ~ r1_lattices(X8922,X8924,esk989_3(X8922,X8923,X8924))
        | ~ r4_lattice3(X8922,X8924,X8923)
        | X8924 = k15_lattice3(X8922,X8923)
        | ~ m1_subset_1(X8924,u1_struct_0(X8922))
        | v2_struct_0(X8922)
        | ~ v10_lattices(X8922)
        | ~ v4_lattice3(X8922)
        | ~ l3_lattices(X8922)
        | v2_struct_0(X8922)
        | ~ l3_lattices(X8922) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

fof(c_0_20,plain,(
    ! [X6643,X6644,X6645] :
      ( ( ~ r3_lattices(X6643,X6644,X6645)
        | r1_lattices(X6643,X6644,X6645)
        | v2_struct_0(X6643)
        | ~ v6_lattices(X6643)
        | ~ v8_lattices(X6643)
        | ~ v9_lattices(X6643)
        | ~ l3_lattices(X6643)
        | ~ m1_subset_1(X6644,u1_struct_0(X6643))
        | ~ m1_subset_1(X6645,u1_struct_0(X6643)) )
      & ( ~ r1_lattices(X6643,X6644,X6645)
        | r3_lattices(X6643,X6644,X6645)
        | v2_struct_0(X6643)
        | ~ v6_lattices(X6643)
        | ~ v8_lattices(X6643)
        | ~ v9_lattices(X6643)
        | ~ l3_lattices(X6643)
        | ~ m1_subset_1(X6644,u1_struct_0(X6643))
        | ~ m1_subset_1(X6645,u1_struct_0(X6643)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_21,negated_conjecture,
    ( r3_lattices(esk1043_0,esk1044_0,k15_lattice3(esk1043_0,X1))
    | ~ r2_hidden(esk1044_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk1044_0,esk1045_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X6624] :
      ( ( l1_lattices(X6624)
        | ~ l3_lattices(X6624) )
      & ( l2_lattices(X6624)
        | ~ l3_lattices(X6624) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_28,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X6679,X6680,X6681] :
      ( v2_struct_0(X6679)
      | ~ v4_lattices(X6679)
      | ~ l2_lattices(X6679)
      | ~ m1_subset_1(X6680,u1_struct_0(X6679))
      | ~ m1_subset_1(X6681,u1_struct_0(X6679))
      | ~ r1_lattices(X6679,X6680,X6681)
      | ~ r1_lattices(X6679,X6681,X6680)
      | X6680 = X6681 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

cnf(c_0_30,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( r3_lattices(esk1043_0,esk1044_0,k15_lattice3(esk1043_0,esk1045_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( v9_lattices(esk1043_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( v8_lattices(esk1043_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( v6_lattices(esk1043_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk1043_0,X1),u1_struct_0(esk1043_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_14]),c_0_16])).

cnf(c_0_36,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_38,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( r1_lattices(esk1043_0,esk1044_0,k15_lattice3(esk1043_0,esk1045_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_14]),c_0_35]),c_0_12])]),c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( l2_lattices(esk1043_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_14])).

cnf(c_0_42,negated_conjecture,
    ( v4_lattices(esk1043_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_43,negated_conjecture,
    ( k15_lattice3(esk1043_0,esk1045_0) != esk1044_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,plain,
    ( r1_lattices(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( r4_lattice3(esk1043_0,esk1044_0,esk1045_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_lattices(esk1043_0,k15_lattice3(esk1043_0,esk1045_0),esk1044_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_12]),c_0_35])]),c_0_43]),c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_13]),c_0_14]),c_0_15]),c_0_12])]),c_0_46]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
