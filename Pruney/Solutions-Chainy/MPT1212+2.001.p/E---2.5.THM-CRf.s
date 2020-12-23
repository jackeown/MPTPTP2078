%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:28 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 147 expanded)
%              Number of clauses        :   27 (  49 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  267 ( 784 expanded)
%              Number of equality atoms :   31 ( 106 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   33 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k3_lattices(X1,k7_lattices(X1,X2),X2) = k6_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattices)).

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattices)).

fof(dt_k7_lattices,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(cc5_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v17_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v11_lattices(X1)
          & v15_lattices(X1)
          & v16_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_lattices)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v17_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => k3_lattices(X1,k7_lattices(X1,X2),X2) = k6_lattices(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t48_lattices])).

fof(c_0_9,plain,(
    ! [X15,X16,X17] :
      ( v2_struct_0(X15)
      | ~ v4_lattices(X15)
      | ~ l2_lattices(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | k3_lattices(X15,X16,X17) = k1_lattices(X15,X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v17_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0) != k6_lattices(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X9,X10,X11] :
      ( ( X11 != k7_lattices(X9,X10)
        | r2_lattices(X9,X11,X10)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ v11_lattices(X9)
        | ~ v16_lattices(X9)
        | ~ l3_lattices(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( ~ r2_lattices(X9,X11,X10)
        | X11 = k7_lattices(X9,X10)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ v11_lattices(X9)
        | ~ v16_lattices(X9)
        | ~ l3_lattices(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattices])])])])])).

cnf(c_0_12,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X12,X13] :
      ( v2_struct_0(X12)
      | ~ l3_lattices(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | m1_subset_1(k7_lattices(X12,X13),u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).

cnf(c_0_16,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( k3_lattices(esk1_0,X1,esk2_0) = k1_lattices(esk1_0,X1,esk2_0)
    | ~ l2_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ v4_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( v2_struct_0(X2)
    | r2_lattices(X2,X1,X3)
    | X1 != k7_lattices(X2,X3)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ v11_lattices(X2)
    | ~ v16_lattices(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,X1),esk2_0) = k1_lattices(esk1_0,k7_lattices(esk1_0,X1),esk2_0)
    | ~ l2_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ v4_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),c_0_14])).

fof(c_0_22,plain,(
    ! [X14] :
      ( ( l1_lattices(X14)
        | ~ l3_lattices(X14) )
      & ( l2_lattices(X14)
        | ~ l3_lattices(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_23,plain,
    ( r2_lattices(X1,k7_lattices(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v16_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]),c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_25,plain,(
    ! [X5] :
      ( ( ~ v2_struct_0(X5)
        | v2_struct_0(X5)
        | ~ v17_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v11_lattices(X5)
        | v2_struct_0(X5)
        | ~ v17_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v15_lattices(X5)
        | v2_struct_0(X5)
        | ~ v17_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v16_lattices(X5)
        | v2_struct_0(X5)
        | ~ v17_lattices(X5)
        | ~ l3_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_lattices])])])])).

cnf(c_0_26,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0) = k1_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)
    | ~ l2_lattices(esk1_0)
    | ~ v4_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_13])).

cnf(c_0_27,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
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

cnf(c_0_29,negated_conjecture,
    ( r2_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)
    | ~ v16_lattices(esk1_0)
    | ~ v11_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_13]),c_0_24]),c_0_19])]),c_0_14])).

cnf(c_0_30,plain,
    ( v11_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0) = k1_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)
    | ~ v4_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_19])])).

cnf(c_0_33,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,plain,(
    ! [X6,X7,X8] :
      ( ( k1_lattices(X6,X7,X8) = k6_lattices(X6)
        | ~ r2_lattices(X6,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) )
      & ( k1_lattices(X6,X8,X7) = k6_lattices(X6)
        | ~ r2_lattices(X6,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) )
      & ( k2_lattices(X6,X7,X8) = k5_lattices(X6)
        | ~ r2_lattices(X6,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) )
      & ( k2_lattices(X6,X8,X7) = k5_lattices(X6)
        | ~ r2_lattices(X6,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) )
      & ( k1_lattices(X6,X7,X8) != k6_lattices(X6)
        | k1_lattices(X6,X8,X7) != k6_lattices(X6)
        | k2_lattices(X6,X7,X8) != k5_lattices(X6)
        | k2_lattices(X6,X8,X7) != k5_lattices(X6)
        | r2_lattices(X6,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_lattices])])])])])).

cnf(c_0_35,negated_conjecture,
    ( r2_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)
    | ~ v16_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_19])]),c_0_14])).

cnf(c_0_36,plain,
    ( v16_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0) != k6_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0) = k1_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_24]),c_0_19])]),c_0_14])).

cnf(c_0_39,plain,
    ( k1_lattices(X1,X2,X3) = k6_lattices(X1)
    | v2_struct_0(X1)
    | ~ r2_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r2_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_31]),c_0_19])]),c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( k1_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0) != k6_lattices(esk1_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( ~ m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_13]),c_0_19])]),c_0_14]),c_0_41])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_18]),c_0_13]),c_0_19])]),c_0_14]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:24:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.12/0.37  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t48_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k3_lattices(X1,k7_lattices(X1,X2),X2)=k6_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattices)).
% 0.12/0.37  fof(redefinition_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 0.12/0.37  fof(d21_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(((((~(v2_struct_0(X1))&v10_lattices(X1))&v11_lattices(X1))&v16_lattices(X1))&l3_lattices(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k7_lattices(X1,X2)<=>r2_lattices(X1,X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattices)).
% 0.12/0.37  fof(dt_k7_lattices, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_lattices)).
% 0.12/0.37  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.12/0.37  fof(cc5_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v17_lattices(X1))=>(((~(v2_struct_0(X1))&v11_lattices(X1))&v15_lattices(X1))&v16_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_lattices)).
% 0.12/0.37  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.12/0.37  fof(d18_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattices(X1,X2,X3)<=>(((k1_lattices(X1,X2,X3)=k6_lattices(X1)&k1_lattices(X1,X3,X2)=k6_lattices(X1))&k2_lattices(X1,X2,X3)=k5_lattices(X1))&k2_lattices(X1,X3,X2)=k5_lattices(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_lattices)).
% 0.12/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v17_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k3_lattices(X1,k7_lattices(X1,X2),X2)=k6_lattices(X1)))), inference(assume_negation,[status(cth)],[t48_lattices])).
% 0.12/0.37  fof(c_0_9, plain, ![X15, X16, X17]:(v2_struct_0(X15)|~v4_lattices(X15)|~l2_lattices(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|k3_lattices(X15,X16,X17)=k1_lattices(X15,X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).
% 0.12/0.37  fof(c_0_10, negated_conjecture, ((((~v2_struct_0(esk1_0)&v10_lattices(esk1_0))&v17_lattices(esk1_0))&l3_lattices(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)!=k6_lattices(esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.12/0.37  fof(c_0_11, plain, ![X9, X10, X11]:((X11!=k7_lattices(X9,X10)|r2_lattices(X9,X11,X10)|~m1_subset_1(X11,u1_struct_0(X9))|(v2_struct_0(X9)|~v10_lattices(X9)|~v11_lattices(X9)|~v16_lattices(X9)|~l3_lattices(X9))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))&(~r2_lattices(X9,X11,X10)|X11=k7_lattices(X9,X10)|~m1_subset_1(X11,u1_struct_0(X9))|(v2_struct_0(X9)|~v10_lattices(X9)|~v11_lattices(X9)|~v16_lattices(X9)|~l3_lattices(X9))|~m1_subset_1(X10,u1_struct_0(X9))|(v2_struct_0(X9)|~l3_lattices(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattices])])])])])).
% 0.12/0.37  cnf(c_0_12, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  fof(c_0_15, plain, ![X12, X13]:(v2_struct_0(X12)|~l3_lattices(X12)|~m1_subset_1(X13,u1_struct_0(X12))|m1_subset_1(k7_lattices(X12,X13),u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).
% 0.12/0.37  cnf(c_0_16, plain, (r2_lattices(X2,X1,X3)|v2_struct_0(X2)|v2_struct_0(X2)|X1!=k7_lattices(X2,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v11_lattices(X2)|~v16_lattices(X2)|~l3_lattices(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (k3_lattices(esk1_0,X1,esk2_0)=k1_lattices(esk1_0,X1,esk2_0)|~l2_lattices(esk1_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~v4_lattices(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.12/0.37  cnf(c_0_18, plain, (v2_struct_0(X1)|m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (l3_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_20, plain, (v2_struct_0(X2)|r2_lattices(X2,X1,X3)|X1!=k7_lattices(X2,X3)|~l3_lattices(X2)|~v10_lattices(X2)|~v11_lattices(X2)|~v16_lattices(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))), inference(cn,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (k3_lattices(esk1_0,k7_lattices(esk1_0,X1),esk2_0)=k1_lattices(esk1_0,k7_lattices(esk1_0,X1),esk2_0)|~l2_lattices(esk1_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~v4_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])]), c_0_14])).
% 0.12/0.37  fof(c_0_22, plain, ![X14]:((l1_lattices(X14)|~l3_lattices(X14))&(l2_lattices(X14)|~l3_lattices(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.12/0.37  cnf(c_0_23, plain, (r2_lattices(X1,k7_lattices(X1,X2),X2)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v16_lattices(X1)|~v11_lattices(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]), c_0_18])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (v10_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  fof(c_0_25, plain, ![X5]:((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v17_lattices(X5))|~l3_lattices(X5))&(v11_lattices(X5)|(v2_struct_0(X5)|~v17_lattices(X5))|~l3_lattices(X5)))&(v15_lattices(X5)|(v2_struct_0(X5)|~v17_lattices(X5))|~l3_lattices(X5)))&(v16_lattices(X5)|(v2_struct_0(X5)|~v17_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_lattices])])])])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)=k1_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)|~l2_lattices(esk1_0)|~v4_lattices(esk1_0)), inference(spm,[status(thm)],[c_0_21, c_0_13])).
% 0.12/0.37  cnf(c_0_27, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.37  fof(c_0_28, plain, ![X4]:(((((((~v2_struct_0(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))&(v4_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v5_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v6_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v7_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v8_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v9_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (r2_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)|~v16_lattices(esk1_0)|~v11_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_13]), c_0_24]), c_0_19])]), c_0_14])).
% 0.12/0.37  cnf(c_0_30, plain, (v11_lattices(X1)|v2_struct_0(X1)|~v17_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (v17_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)=k1_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)|~v4_lattices(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_19])])).
% 0.12/0.37  cnf(c_0_33, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  fof(c_0_34, plain, ![X6, X7, X8]:(((((k1_lattices(X6,X7,X8)=k6_lattices(X6)|~r2_lattices(X6,X7,X8)|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X7,u1_struct_0(X6))|(v2_struct_0(X6)|~l3_lattices(X6)))&(k1_lattices(X6,X8,X7)=k6_lattices(X6)|~r2_lattices(X6,X7,X8)|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X7,u1_struct_0(X6))|(v2_struct_0(X6)|~l3_lattices(X6))))&(k2_lattices(X6,X7,X8)=k5_lattices(X6)|~r2_lattices(X6,X7,X8)|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X7,u1_struct_0(X6))|(v2_struct_0(X6)|~l3_lattices(X6))))&(k2_lattices(X6,X8,X7)=k5_lattices(X6)|~r2_lattices(X6,X7,X8)|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X7,u1_struct_0(X6))|(v2_struct_0(X6)|~l3_lattices(X6))))&(k1_lattices(X6,X7,X8)!=k6_lattices(X6)|k1_lattices(X6,X8,X7)!=k6_lattices(X6)|k2_lattices(X6,X7,X8)!=k5_lattices(X6)|k2_lattices(X6,X8,X7)!=k5_lattices(X6)|r2_lattices(X6,X7,X8)|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X7,u1_struct_0(X6))|(v2_struct_0(X6)|~l3_lattices(X6)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_lattices])])])])])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (r2_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)|~v16_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_19])]), c_0_14])).
% 0.12/0.37  cnf(c_0_36, plain, (v16_lattices(X1)|v2_struct_0(X1)|~v17_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)!=k6_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (k3_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)=k1_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_24]), c_0_19])]), c_0_14])).
% 0.12/0.37  cnf(c_0_39, plain, (k1_lattices(X1,X2,X3)=k6_lattices(X1)|v2_struct_0(X1)|~r2_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (r2_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_31]), c_0_19])]), c_0_14])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (k1_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0)!=k6_lattices(esk1_0)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (~m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_13]), c_0_19])]), c_0_14]), c_0_41])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_18]), c_0_13]), c_0_19])]), c_0_14]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 44
% 0.12/0.37  # Proof object clause steps            : 27
% 0.12/0.37  # Proof object formula steps           : 17
% 0.12/0.37  # Proof object conjectures             : 20
% 0.12/0.37  # Proof object clause conjectures      : 17
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 14
% 0.12/0.37  # Proof object initial formulas used   : 8
% 0.12/0.37  # Proof object generating inferences   : 10
% 0.12/0.37  # Proof object simplifying inferences  : 35
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 8
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 28
% 0.12/0.37  # Removed in clause preprocessing      : 2
% 0.12/0.37  # Initial clauses in saturation        : 26
% 0.12/0.37  # Processed clauses                    : 64
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 64
% 0.12/0.37  # Other redundant clauses eliminated   : 1
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 3
% 0.12/0.37  # Backward-rewritten                   : 5
% 0.12/0.37  # Generated clauses                    : 19
% 0.12/0.37  # ...of the previous two non-trivial   : 19
% 0.12/0.37  # Contextual simplify-reflections      : 1
% 0.12/0.37  # Paramodulations                      : 18
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 1
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 29
% 0.12/0.37  #    Positive orientable unit clauses  : 8
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 3
% 0.12/0.37  #    Non-unit-clauses                  : 18
% 0.12/0.37  # Current number of unprocessed clauses: 7
% 0.12/0.37  # ...number of literals in the above   : 48
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 34
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 727
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 149
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.12/0.37  # Unit Clause-clause subsumption calls : 2
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 5
% 0.12/0.37  # BW rewrite match successes           : 4
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3005
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.029 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.034 s
% 0.12/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
