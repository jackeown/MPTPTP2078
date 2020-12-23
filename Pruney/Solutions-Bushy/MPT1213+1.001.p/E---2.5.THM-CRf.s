%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1213+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:55 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 477 expanded)
%              Number of clauses        :   37 ( 165 expanded)
%              Number of leaves         :    5 ( 114 expanded)
%              Depth                    :    9
%              Number of atoms          :  263 (2595 expanded)
%              Number of equality atoms :   44 ( 359 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattices)).

fof(t49_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v17_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k7_lattices(X1,k7_lattices(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).

fof(dt_k7_lattices,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(cc5_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v17_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v11_lattices(X1)
          & v15_lattices(X1)
          & v16_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_lattices)).

fof(c_0_5,plain,(
    ! [X8,X9,X10] :
      ( ( X10 != k7_lattices(X8,X9)
        | r2_lattices(X8,X10,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ v11_lattices(X8)
        | ~ v16_lattices(X8)
        | ~ l3_lattices(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ l3_lattices(X8) )
      & ( ~ r2_lattices(X8,X10,X9)
        | X10 = k7_lattices(X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ v11_lattices(X8)
        | ~ v16_lattices(X8)
        | ~ l3_lattices(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ l3_lattices(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattices])])])])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v17_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => k7_lattices(X1,k7_lattices(X1,X2)) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t49_lattices])).

cnf(c_0_7,plain,
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

fof(c_0_8,plain,(
    ! [X11,X12] :
      ( v2_struct_0(X11)
      | ~ l3_lattices(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | m1_subset_1(k7_lattices(X11,X12),u1_struct_0(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_lattices])])])).

fof(c_0_9,plain,(
    ! [X4] :
      ( ( ~ v2_struct_0(X4)
        | v2_struct_0(X4)
        | ~ v17_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v11_lattices(X4)
        | v2_struct_0(X4)
        | ~ v17_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v15_lattices(X4)
        | v2_struct_0(X4)
        | ~ v17_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v16_lattices(X4)
        | v2_struct_0(X4)
        | ~ v17_lattices(X4)
        | ~ l3_lattices(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_lattices])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v17_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & k7_lattices(esk1_0,k7_lattices(esk1_0,esk2_0)) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

cnf(c_0_11,plain,
    ( v2_struct_0(X2)
    | r2_lattices(X2,X1,X3)
    | X1 != k7_lattices(X2,X3)
    | ~ l3_lattices(X2)
    | ~ v11_lattices(X2)
    | ~ v16_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k7_lattices(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v16_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v17_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v11_lattices(X1)
    | v2_struct_0(X1)
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_18,plain,(
    ! [X5,X6,X7] :
      ( ( k1_lattices(X5,X6,X7) = k6_lattices(X5)
        | ~ r2_lattices(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l3_lattices(X5) )
      & ( k1_lattices(X5,X7,X6) = k6_lattices(X5)
        | ~ r2_lattices(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l3_lattices(X5) )
      & ( k2_lattices(X5,X6,X7) = k5_lattices(X5)
        | ~ r2_lattices(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l3_lattices(X5) )
      & ( k2_lattices(X5,X7,X6) = k5_lattices(X5)
        | ~ r2_lattices(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l3_lattices(X5) )
      & ( k1_lattices(X5,X6,X7) != k6_lattices(X5)
        | k1_lattices(X5,X7,X6) != k6_lattices(X5)
        | k2_lattices(X5,X6,X7) != k5_lattices(X5)
        | k2_lattices(X5,X7,X6) != k5_lattices(X5)
        | r2_lattices(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l3_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_lattices])])])])])).

cnf(c_0_19,plain,
    ( r2_lattices(X1,k7_lattices(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v16_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( v16_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v11_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_23,plain,
    ( k1_lattices(X1,X2,X3) = k6_lattices(X1)
    | v2_struct_0(X1)
    | ~ r2_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r2_lattices(esk1_0,k7_lattices(esk1_0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_15])]),c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk1_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_15]),c_0_16])).

cnf(c_0_27,plain,
    ( k1_lattices(X1,X2,X3) = k6_lattices(X1)
    | v2_struct_0(X1)
    | ~ r2_lattices(X1,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k2_lattices(X1,X2,X3) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ r2_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k2_lattices(X1,X2,X3) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ r2_lattices(X1,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( k1_lattices(esk1_0,X1,X2) = k6_lattices(esk1_0)
    | ~ r2_lattices(esk1_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_15]),c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( r2_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k7_lattices(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( k1_lattices(esk1_0,X1,X2) = k6_lattices(esk1_0)
    | ~ r2_lattices(esk1_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_15]),c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( k2_lattices(esk1_0,X1,X2) = k5_lattices(esk1_0)
    | ~ r2_lattices(esk1_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_15]),c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( k2_lattices(esk1_0,X1,X2) = k5_lattices(esk1_0)
    | ~ r2_lattices(esk1_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_15]),c_0_16])).

cnf(c_0_38,plain,
    ( X2 = k7_lattices(X1,X3)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ v16_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ r2_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r2_lattices(esk1_0,X1,X2)
    | k1_lattices(esk1_0,X2,X1) != k6_lattices(esk1_0)
    | k1_lattices(esk1_0,X1,X2) != k6_lattices(esk1_0)
    | k2_lattices(esk1_0,X2,X1) != k5_lattices(esk1_0)
    | k2_lattices(esk1_0,X1,X2) != k5_lattices(esk1_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_15]),c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( k1_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0) = k6_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25]),c_0_34])])).

cnf(c_0_41,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk2_0)) = k6_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33]),c_0_34]),c_0_25])])).

cnf(c_0_42,negated_conjecture,
    ( k2_lattices(esk1_0,k7_lattices(esk1_0,esk2_0),esk2_0) = k5_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_25]),c_0_34])])).

cnf(c_0_43,negated_conjecture,
    ( k2_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk2_0)) = k5_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_34]),c_0_25])])).

cnf(c_0_44,negated_conjecture,
    ( X1 = k7_lattices(esk1_0,X2)
    | ~ r2_lattices(esk1_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_20]),c_0_21]),c_0_22]),c_0_15])]),c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( r2_lattices(esk1_0,esk2_0,k7_lattices(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_34]),c_0_25])])).

cnf(c_0_46,negated_conjecture,
    ( k7_lattices(esk1_0,k7_lattices(esk1_0,esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_34]),c_0_25])]),c_0_46]),
    [proof]).

%------------------------------------------------------------------------------
