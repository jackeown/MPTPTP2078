%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattices__t49_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:03 EDT 2019

% Result     : Theorem 0.55s
% Output     : CNFRefutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 461 expanded)
%              Number of clauses        :   31 ( 149 expanded)
%              Number of leaves         :    5 ( 114 expanded)
%              Depth                    :   12
%              Number of atoms          :  238 (2561 expanded)
%              Number of equality atoms :   35 ( 350 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   33 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d21_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( ( ~ v2_struct_0(X1)
              & v10_lattices(X1)
              & v11_lattices(X1)
              & v16_lattices(X1)
              & l3_lattices(X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( X3 = k7_lattices(X1,X2)
                <=> r2_lattices(X1,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t49_lattices.p',d21_lattices)).

fof(dt_k7_lattices,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t49_lattices.p',dt_k7_lattices)).

fof(t49_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k7_lattices(X1,k7_lattices(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t49_lattices.p',t49_lattices)).

fof(cc5_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v17_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v11_lattices(X1)
          & v15_lattices(X1)
          & v16_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t49_lattices.p',cc5_lattices)).

fof(d18_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_lattices(X1,X2,X3)
              <=> ( k1_lattices(X1,X2,X3) = k6_lattices(X1)
                  & k1_lattices(X1,X3,X2) = k6_lattices(X1)
                  & k2_lattices(X1,X2,X3) = k5_lattices(X1)
                  & k2_lattices(X1,X3,X2) = k5_lattices(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t49_lattices.p',d18_lattices)).

fof(c_0_5,plain,(
    ! [X18,X19,X20] :
      ( ( X20 != k7_lattices(X18,X19)
        | r2_lattices(X18,X20,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ v11_lattices(X18)
        | ~ v16_lattices(X18)
        | ~ l3_lattices(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( ~ r2_lattices(X18,X20,X19)
        | X20 = k7_lattices(X18,X19)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v10_lattices(X18)
        | ~ v11_lattices(X18)
        | ~ v16_lattices(X18)
        | ~ l3_lattices(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattices])])])])])).

cnf(c_0_6,plain,
    ( r2_lattices(X2,X1,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X2)
    | X1 != k7_lattices(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v11_lattices(X2)
    | ~ v16_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_7,plain,(
    ! [X39,X40] :
      ( v2_struct_0(X39)
      | ~ l3_lattices(X39)
      | ~ m1_subset_1(X40,u1_struct_0(X39))
      | m1_subset_1(k7_lattices(X39,X40),u1_struct_0(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v17_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => k7_lattices(X1,k7_lattices(X1,X2)) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t49_lattices])).

cnf(c_0_9,plain,
    ( v2_struct_0(X2)
    | r2_lattices(X2,X1,X3)
    | X1 != k7_lattices(X2,X3)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ v11_lattices(X2)
    | ~ v16_lattices(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v17_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & k7_lattices(esk1_0,k7_lattices(esk1_0,esk2_0)) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_12,plain,
    ( r2_lattices(X1,k7_lattices(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v16_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X84] :
      ( ( ~ v2_struct_0(X84)
        | v2_struct_0(X84)
        | ~ v17_lattices(X84)
        | ~ l3_lattices(X84) )
      & ( v11_lattices(X84)
        | v2_struct_0(X84)
        | ~ v17_lattices(X84)
        | ~ l3_lattices(X84) )
      & ( v15_lattices(X84)
        | v2_struct_0(X84)
        | ~ v17_lattices(X84)
        | ~ l3_lattices(X84) )
      & ( v16_lattices(X84)
        | v2_struct_0(X84)
        | ~ v17_lattices(X84)
        | ~ l3_lattices(X84) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_lattices])])])])).

cnf(c_0_18,negated_conjecture,
    ( r2_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)
    | ~ v16_lattices(esk1_0)
    | ~ v11_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_19,plain,
    ( v16_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_21,plain,(
    ! [X15,X16,X17] :
      ( ( k1_lattices(X15,X16,X17) = k6_lattices(X15)
        | ~ r2_lattices(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( k1_lattices(X15,X17,X16) = k6_lattices(X15)
        | ~ r2_lattices(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( k2_lattices(X15,X16,X17) = k5_lattices(X15)
        | ~ r2_lattices(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( k2_lattices(X15,X17,X16) = k5_lattices(X15)
        | ~ r2_lattices(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( k1_lattices(X15,X16,X17) != k6_lattices(X15)
        | k1_lattices(X15,X17,X16) != k6_lattices(X15)
        | k2_lattices(X15,X16,X17) != k5_lattices(X15)
        | k2_lattices(X15,X17,X16) != k5_lattices(X15)
        | r2_lattices(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_lattices])])])])])).

cnf(c_0_22,negated_conjecture,
    ( r2_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)
    | ~ v11_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_14]),c_0_20])]),c_0_16])).

cnf(c_0_23,plain,
    ( v11_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_lattices(X1,X2,X3) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ r2_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_14]),c_0_20])]),c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_13]),c_0_14])]),c_0_16])).

cnf(c_0_27,plain,
    ( k1_lattices(X1,X2,X3) = k6_lattices(X1)
    | v2_struct_0(X1)
    | ~ r2_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k1_lattices(X1,X2,X3) = k6_lattices(X1)
    | v2_struct_0(X1)
    | ~ r2_lattices(X1,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_lattices(X1,X2,X3) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ r2_lattices(X1,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( X2 = k7_lattices(X1,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | ~ r2_lattices(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ v16_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_31,plain,
    ( r2_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != k6_lattices(X1)
    | k1_lattices(X1,X3,X2) != k6_lattices(X1)
    | k2_lattices(X1,X2,X3) != k5_lattices(X1)
    | k2_lattices(X1,X3,X2) != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( k2_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0) = k5_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_13]),c_0_26]),c_0_14])]),c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( k1_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0) = k6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_13]),c_0_26]),c_0_14])]),c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk2_0)) = k6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_25]),c_0_26]),c_0_13]),c_0_14])]),c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( k2_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk2_0)) = k5_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_26]),c_0_13]),c_0_14])]),c_0_16])).

cnf(c_0_36,plain,
    ( X2 = k7_lattices(X1,X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ v16_lattices(X1)
    | ~ r2_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r2_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_26]),c_0_13]),c_0_14])]),c_0_16]),c_0_34]),c_0_35])])).

cnf(c_0_38,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( ~ v16_lattices(esk1_0)
    | ~ v11_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_26]),c_0_13]),c_0_14]),c_0_15])]),c_0_38]),c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( ~ v11_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_19]),c_0_14]),c_0_20])]),c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_23]),c_0_14]),c_0_20])]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
