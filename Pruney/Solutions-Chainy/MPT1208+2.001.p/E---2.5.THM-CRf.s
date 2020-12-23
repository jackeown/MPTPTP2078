%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:26 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 239 expanded)
%              Number of clauses        :   36 (  84 expanded)
%              Number of leaves         :    9 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  268 (1174 expanded)
%              Number of equality atoms :   43 ( 151 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k6_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => m1_subset_1(k6_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(t43_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v14_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattices(X1,k6_lattices(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).

fof(d17_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ( v14_lattices(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( X2 = k6_lattices(X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( k1_lattices(X1,X2,X3) = X2
                    & k1_lattices(X1,X3,X2) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattices)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(d3_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k1_lattices(X1,X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

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

fof(c_0_9,plain,(
    ! [X15] :
      ( v2_struct_0(X15)
      | ~ l2_lattices(X15)
      | m1_subset_1(k6_lattices(X15),u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_lattices])])])).

fof(c_0_10,plain,(
    ! [X16] :
      ( ( l1_lattices(X16)
        | ~ l3_lattices(X16) )
      & ( l2_lattices(X16)
        | ~ l3_lattices(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v14_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => k4_lattices(X1,k6_lattices(X1),X2) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t43_lattices])).

fof(c_0_12,plain,(
    ! [X8,X9,X10] :
      ( ( k1_lattices(X8,X9,X10) = X9
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | X9 != k6_lattices(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v14_lattices(X8)
        | v2_struct_0(X8)
        | ~ l2_lattices(X8) )
      & ( k1_lattices(X8,X10,X9) = X9
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | X9 != k6_lattices(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v14_lattices(X8)
        | v2_struct_0(X8)
        | ~ l2_lattices(X8) )
      & ( m1_subset_1(esk1_2(X8,X9),u1_struct_0(X8))
        | X9 = k6_lattices(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v14_lattices(X8)
        | v2_struct_0(X8)
        | ~ l2_lattices(X8) )
      & ( k1_lattices(X8,X9,esk1_2(X8,X9)) != X9
        | k1_lattices(X8,esk1_2(X8,X9),X9) != X9
        | X9 = k6_lattices(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ v14_lattices(X8)
        | v2_struct_0(X8)
        | ~ l2_lattices(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattices])])])])])])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v10_lattices(esk2_0)
    & v14_lattices(esk2_0)
    & l3_lattices(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & k4_lattices(esk2_0,k6_lattices(esk2_0),esk3_0) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_16,plain,(
    ! [X5,X6,X7] :
      ( v2_struct_0(X5)
      | ~ v6_lattices(X5)
      | ~ l1_lattices(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | k4_lattices(X5,X6,X7) = k4_lattices(X5,X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_17,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k6_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v14_lattices(X1)
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X17,X18,X19] :
      ( v2_struct_0(X17)
      | ~ v6_lattices(X17)
      | ~ l1_lattices(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | k4_lattices(X17,X18,X19) = k2_lattices(X17,X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

cnf(c_0_19,plain,
    ( m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k1_lattices(X1,X2,k6_lattices(X1)) = k6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v14_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( v14_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(k6_lattices(esk2_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k4_lattices(esk2_0,X1,esk3_0) = k4_lattices(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ l1_lattices(esk2_0)
    | ~ v6_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_21])).

fof(c_0_29,plain,(
    ! [X12,X13,X14] :
      ( ( ~ r1_lattices(X12,X13,X14)
        | k1_lattices(X12,X13,X14) = X14
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l2_lattices(X12) )
      & ( k1_lattices(X12,X13,X14) != X14
        | r1_lattices(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ l2_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

cnf(c_0_30,negated_conjecture,
    ( k1_lattices(esk2_0,esk3_0,k6_lattices(esk2_0)) = k6_lattices(esk2_0)
    | ~ l2_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_23]),c_0_25])]),c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( k2_lattices(esk2_0,X1,k6_lattices(esk2_0)) = k4_lattices(esk2_0,X1,k6_lattices(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ l1_lattices(esk2_0)
    | ~ v6_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( k4_lattices(esk2_0,k6_lattices(esk2_0),esk3_0) = k4_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))
    | ~ l1_lattices(esk2_0)
    | ~ v6_lattices(esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_33,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_34,plain,(
    ! [X4] :
      ( ( ~ v2_struct_0(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v4_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v5_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v6_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v7_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v8_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v9_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_35,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k1_lattices(esk2_0,esk3_0,k6_lattices(esk2_0)) = k6_lattices(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_14]),c_0_20])])).

cnf(c_0_37,negated_conjecture,
    ( k2_lattices(esk2_0,esk3_0,k6_lattices(esk2_0)) = k4_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))
    | ~ l1_lattices(esk2_0)
    | ~ v6_lattices(esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( k4_lattices(esk2_0,k6_lattices(esk2_0),esk3_0) = k4_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))
    | ~ v6_lattices(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_20])])).

cnf(c_0_39,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_41,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r1_lattices(X20,X21,X22)
        | k2_lattices(X20,X21,X22) = X21
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v8_lattices(X20)
        | ~ v9_lattices(X20)
        | ~ l3_lattices(X20) )
      & ( k2_lattices(X20,X21,X22) != X21
        | r1_lattices(X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v8_lattices(X20)
        | ~ v9_lattices(X20)
        | ~ l3_lattices(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_42,negated_conjecture,
    ( r1_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))
    | ~ l2_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_27]),c_0_23])]),c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( k2_lattices(esk2_0,esk3_0,k6_lattices(esk2_0)) = k4_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))
    | ~ v6_lattices(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_20])])).

cnf(c_0_44,negated_conjecture,
    ( k4_lattices(esk2_0,k6_lattices(esk2_0),esk3_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( k4_lattices(esk2_0,k6_lattices(esk2_0),esk3_0) = k4_lattices(esk2_0,esk3_0,k6_lattices(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_20])]),c_0_21])).

cnf(c_0_46,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r1_lattices(esk2_0,esk3_0,k6_lattices(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_14]),c_0_20])])).

cnf(c_0_48,negated_conjecture,
    ( k2_lattices(esk2_0,esk3_0,k6_lattices(esk2_0)) = k4_lattices(esk2_0,esk3_0,k6_lattices(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_39]),c_0_40]),c_0_20])]),c_0_21])).

cnf(c_0_49,negated_conjecture,
    ( k4_lattices(esk2_0,esk3_0,k6_lattices(esk2_0)) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( ~ v9_lattices(esk2_0)
    | ~ v8_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_27]),c_0_23]),c_0_20])]),c_0_49]),c_0_21])).

cnf(c_0_51,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( ~ v9_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_40]),c_0_20])]),c_0_21])).

cnf(c_0_53,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_40]),c_0_20])]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:55:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.18/0.37  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.18/0.37  #
% 0.18/0.37  # Preprocessing time       : 0.028 s
% 0.18/0.37  # Presaturation interreduction done
% 0.18/0.37  
% 0.18/0.37  # Proof found!
% 0.18/0.37  # SZS status Theorem
% 0.18/0.37  # SZS output start CNFRefutation
% 0.18/0.37  fof(dt_k6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>m1_subset_1(k6_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_lattices)).
% 0.18/0.37  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.18/0.37  fof(t43_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v14_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,k6_lattices(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_lattices)).
% 0.18/0.37  fof(d17_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>(v14_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k6_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k1_lattices(X1,X2,X3)=X2&k1_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattices)).
% 0.18/0.37  fof(commutativity_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 0.18/0.37  fof(redefinition_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 0.18/0.37  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 0.18/0.37  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.18/0.37  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 0.18/0.37  fof(c_0_9, plain, ![X15]:(v2_struct_0(X15)|~l2_lattices(X15)|m1_subset_1(k6_lattices(X15),u1_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_lattices])])])).
% 0.18/0.37  fof(c_0_10, plain, ![X16]:((l1_lattices(X16)|~l3_lattices(X16))&(l2_lattices(X16)|~l3_lattices(X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.18/0.37  fof(c_0_11, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v14_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,k6_lattices(X1),X2)=X2))), inference(assume_negation,[status(cth)],[t43_lattices])).
% 0.18/0.37  fof(c_0_12, plain, ![X8, X9, X10]:(((k1_lattices(X8,X9,X10)=X9|~m1_subset_1(X10,u1_struct_0(X8))|X9!=k6_lattices(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~v14_lattices(X8)|(v2_struct_0(X8)|~l2_lattices(X8)))&(k1_lattices(X8,X10,X9)=X9|~m1_subset_1(X10,u1_struct_0(X8))|X9!=k6_lattices(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~v14_lattices(X8)|(v2_struct_0(X8)|~l2_lattices(X8))))&((m1_subset_1(esk1_2(X8,X9),u1_struct_0(X8))|X9=k6_lattices(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~v14_lattices(X8)|(v2_struct_0(X8)|~l2_lattices(X8)))&(k1_lattices(X8,X9,esk1_2(X8,X9))!=X9|k1_lattices(X8,esk1_2(X8,X9),X9)!=X9|X9=k6_lattices(X8)|~m1_subset_1(X9,u1_struct_0(X8))|~v14_lattices(X8)|(v2_struct_0(X8)|~l2_lattices(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattices])])])])])])).
% 0.18/0.37  cnf(c_0_13, plain, (v2_struct_0(X1)|m1_subset_1(k6_lattices(X1),u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  cnf(c_0_14, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.37  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk2_0)&v10_lattices(esk2_0))&v14_lattices(esk2_0))&l3_lattices(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&k4_lattices(esk2_0,k6_lattices(esk2_0),esk3_0)!=esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.18/0.37  fof(c_0_16, plain, ![X5, X6, X7]:(v2_struct_0(X5)|~v6_lattices(X5)|~l1_lattices(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))|k4_lattices(X5,X6,X7)=k4_lattices(X5,X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).
% 0.18/0.37  cnf(c_0_17, plain, (k1_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k6_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v14_lattices(X1)|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.37  fof(c_0_18, plain, ![X17, X18, X19]:(v2_struct_0(X17)|~v6_lattices(X17)|~l1_lattices(X17)|~m1_subset_1(X18,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|k4_lattices(X17,X18,X19)=k2_lattices(X17,X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).
% 0.18/0.37  cnf(c_0_19, plain, (m1_subset_1(k6_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.18/0.37  cnf(c_0_20, negated_conjecture, (l3_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_22, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.37  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_24, plain, (k1_lattices(X1,X2,k6_lattices(X1))=k6_lattices(X1)|v2_struct_0(X1)|~v14_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]), c_0_13])).
% 0.18/0.37  cnf(c_0_25, negated_conjecture, (v14_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_26, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.37  cnf(c_0_27, negated_conjecture, (m1_subset_1(k6_lattices(esk2_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.18/0.37  cnf(c_0_28, negated_conjecture, (k4_lattices(esk2_0,X1,esk3_0)=k4_lattices(esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~l1_lattices(esk2_0)|~v6_lattices(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_21])).
% 0.18/0.37  fof(c_0_29, plain, ![X12, X13, X14]:((~r1_lattices(X12,X13,X14)|k1_lattices(X12,X13,X14)=X14|~m1_subset_1(X14,u1_struct_0(X12))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~l2_lattices(X12)))&(k1_lattices(X12,X13,X14)!=X14|r1_lattices(X12,X13,X14)|~m1_subset_1(X14,u1_struct_0(X12))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~l2_lattices(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.18/0.37  cnf(c_0_30, negated_conjecture, (k1_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))=k6_lattices(esk2_0)|~l2_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_23]), c_0_25])]), c_0_21])).
% 0.18/0.37  cnf(c_0_31, negated_conjecture, (k2_lattices(esk2_0,X1,k6_lattices(esk2_0))=k4_lattices(esk2_0,X1,k6_lattices(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~l1_lattices(esk2_0)|~v6_lattices(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_21])).
% 0.18/0.37  cnf(c_0_32, negated_conjecture, (k4_lattices(esk2_0,k6_lattices(esk2_0),esk3_0)=k4_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))|~l1_lattices(esk2_0)|~v6_lattices(esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 0.18/0.37  cnf(c_0_33, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.37  fof(c_0_34, plain, ![X4]:(((((((~v2_struct_0(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))&(v4_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v5_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v6_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v7_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v8_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v9_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.18/0.37  cnf(c_0_35, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k1_lattices(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.37  cnf(c_0_36, negated_conjecture, (k1_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))=k6_lattices(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_14]), c_0_20])])).
% 0.18/0.37  cnf(c_0_37, negated_conjecture, (k2_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))=k4_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))|~l1_lattices(esk2_0)|~v6_lattices(esk2_0)), inference(spm,[status(thm)],[c_0_31, c_0_23])).
% 0.18/0.37  cnf(c_0_38, negated_conjecture, (k4_lattices(esk2_0,k6_lattices(esk2_0),esk3_0)=k4_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))|~v6_lattices(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_20])])).
% 0.18/0.37  cnf(c_0_39, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.37  cnf(c_0_40, negated_conjecture, (v10_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  fof(c_0_41, plain, ![X20, X21, X22]:((~r1_lattices(X20,X21,X22)|k2_lattices(X20,X21,X22)=X21|~m1_subset_1(X22,u1_struct_0(X20))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~v8_lattices(X20)|~v9_lattices(X20)|~l3_lattices(X20)))&(k2_lattices(X20,X21,X22)!=X21|r1_lattices(X20,X21,X22)|~m1_subset_1(X22,u1_struct_0(X20))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~v8_lattices(X20)|~v9_lattices(X20)|~l3_lattices(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.18/0.37  cnf(c_0_42, negated_conjecture, (r1_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))|~l2_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_27]), c_0_23])]), c_0_21])).
% 0.18/0.37  cnf(c_0_43, negated_conjecture, (k2_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))=k4_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))|~v6_lattices(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_33]), c_0_20])])).
% 0.18/0.37  cnf(c_0_44, negated_conjecture, (k4_lattices(esk2_0,k6_lattices(esk2_0),esk3_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_45, negated_conjecture, (k4_lattices(esk2_0,k6_lattices(esk2_0),esk3_0)=k4_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_20])]), c_0_21])).
% 0.18/0.37  cnf(c_0_46, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.18/0.37  cnf(c_0_47, negated_conjecture, (r1_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_14]), c_0_20])])).
% 0.18/0.37  cnf(c_0_48, negated_conjecture, (k2_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))=k4_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_39]), c_0_40]), c_0_20])]), c_0_21])).
% 0.18/0.37  cnf(c_0_49, negated_conjecture, (k4_lattices(esk2_0,esk3_0,k6_lattices(esk2_0))!=esk3_0), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.18/0.37  cnf(c_0_50, negated_conjecture, (~v9_lattices(esk2_0)|~v8_lattices(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_27]), c_0_23]), c_0_20])]), c_0_49]), c_0_21])).
% 0.18/0.37  cnf(c_0_51, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.37  cnf(c_0_52, negated_conjecture, (~v9_lattices(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_40]), c_0_20])]), c_0_21])).
% 0.18/0.37  cnf(c_0_53, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.37  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_40]), c_0_20])]), c_0_21]), ['proof']).
% 0.18/0.37  # SZS output end CNFRefutation
% 0.18/0.37  # Proof object total steps             : 55
% 0.18/0.37  # Proof object clause steps            : 36
% 0.18/0.37  # Proof object formula steps           : 19
% 0.18/0.37  # Proof object conjectures             : 26
% 0.18/0.37  # Proof object clause conjectures      : 23
% 0.18/0.37  # Proof object formula conjectures     : 3
% 0.18/0.37  # Proof object initial clauses used    : 17
% 0.18/0.37  # Proof object initial formulas used   : 9
% 0.18/0.37  # Proof object generating inferences   : 17
% 0.18/0.37  # Proof object simplifying inferences  : 44
% 0.18/0.37  # Training examples: 0 positive, 0 negative
% 0.18/0.37  # Parsed axioms                        : 9
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 26
% 0.18/0.37  # Removed in clause preprocessing      : 1
% 0.18/0.37  # Initial clauses in saturation        : 25
% 0.18/0.37  # Processed clauses                    : 108
% 0.18/0.37  # ...of these trivial                  : 0
% 0.18/0.37  # ...subsumed                          : 1
% 0.18/0.37  # ...remaining for further processing  : 107
% 0.18/0.37  # Other redundant clauses eliminated   : 2
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 16
% 0.18/0.37  # Backward-rewritten                   : 13
% 0.18/0.37  # Generated clauses                    : 80
% 0.18/0.37  # ...of the previous two non-trivial   : 77
% 0.18/0.37  # Contextual simplify-reflections      : 3
% 0.18/0.37  # Paramodulations                      : 78
% 0.18/0.37  # Factorizations                       : 0
% 0.18/0.37  # Equation resolutions                 : 2
% 0.18/0.37  # Propositional unsat checks           : 0
% 0.18/0.37  #    Propositional check models        : 0
% 0.18/0.37  #    Propositional check unsatisfiable : 0
% 0.18/0.37  #    Propositional clauses             : 0
% 0.18/0.37  #    Propositional clauses after purity: 0
% 0.18/0.37  #    Propositional unsat core size     : 0
% 0.18/0.37  #    Propositional preprocessing time  : 0.000
% 0.18/0.37  #    Propositional encoding time       : 0.000
% 0.18/0.37  #    Propositional solver time         : 0.000
% 0.18/0.37  #    Success case prop preproc time    : 0.000
% 0.18/0.37  #    Success case prop encoding time   : 0.000
% 0.18/0.37  #    Success case prop solver time     : 0.000
% 0.18/0.37  # Current number of processed clauses  : 51
% 0.18/0.37  #    Positive orientable unit clauses  : 15
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 3
% 0.18/0.37  #    Non-unit-clauses                  : 33
% 0.18/0.37  # Current number of unprocessed clauses: 19
% 0.18/0.37  # ...number of literals in the above   : 90
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 54
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 448
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 168
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 20
% 0.18/0.37  # Unit Clause-clause subsumption calls : 27
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 15
% 0.18/0.37  # BW rewrite match successes           : 10
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 4555
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.036 s
% 0.18/0.37  # System time              : 0.002 s
% 0.18/0.37  # Total time               : 0.038 s
% 0.18/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
