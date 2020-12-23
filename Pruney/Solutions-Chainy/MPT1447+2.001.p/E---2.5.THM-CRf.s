%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:53 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 672 expanded)
%              Number of clauses        :   39 ( 213 expanded)
%              Number of leaves         :    7 ( 174 expanded)
%              Depth                    :   12
%              Number of atoms          :  328 (5362 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   25 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => ( ( v14_lattices(X1)
              & v14_lattices(X2) )
          <=> v14_lattices(k7_filter_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_filter_1)).

fof(cc4_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v15_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v13_lattices(X1)
          & v14_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_lattices)).

fof(dt_k7_filter_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & ~ v2_struct_0(X2)
        & l3_lattices(X2) )
     => ( v3_lattices(k7_filter_1(X1,X2))
        & l3_lattices(k7_filter_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_filter_1)).

fof(fc2_filter_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1)
        & ~ v2_struct_0(X2)
        & l3_lattices(X2) )
     => ( ~ v2_struct_0(k7_filter_1(X1,X2))
        & v3_lattices(k7_filter_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_filter_1)).

fof(t42_filter_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => ( ( v15_lattices(X1)
              & v15_lattices(X2) )
          <=> v15_lattices(k7_filter_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_filter_1)).

fof(t40_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => ( ( v13_lattices(X1)
              & v13_lattices(X2) )
          <=> v13_lattices(k7_filter_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_filter_1)).

fof(cc3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v13_lattices(X1)
          & v14_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v15_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_lattices)).

fof(c_0_7,plain,(
    ! [X11,X12] :
      ( ( ~ v14_lattices(X11)
        | ~ v14_lattices(X12)
        | v14_lattices(k7_filter_1(X11,X12))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ l3_lattices(X12)
        | v2_struct_0(X11)
        | ~ v10_lattices(X11)
        | ~ l3_lattices(X11) )
      & ( v14_lattices(X11)
        | ~ v14_lattices(k7_filter_1(X11,X12))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ l3_lattices(X12)
        | v2_struct_0(X11)
        | ~ v10_lattices(X11)
        | ~ l3_lattices(X11) )
      & ( v14_lattices(X12)
        | ~ v14_lattices(k7_filter_1(X11,X12))
        | v2_struct_0(X12)
        | ~ v10_lattices(X12)
        | ~ l3_lattices(X12)
        | v2_struct_0(X11)
        | ~ v10_lattices(X11)
        | ~ l3_lattices(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_filter_1])])])])])).

fof(c_0_8,plain,(
    ! [X4] :
      ( ( ~ v2_struct_0(X4)
        | v2_struct_0(X4)
        | ~ v15_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v13_lattices(X4)
        | v2_struct_0(X4)
        | ~ v15_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v14_lattices(X4)
        | v2_struct_0(X4)
        | ~ v15_lattices(X4)
        | ~ l3_lattices(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_lattices])])])])).

fof(c_0_9,plain,(
    ! [X5,X6] :
      ( ( v3_lattices(k7_filter_1(X5,X6))
        | v2_struct_0(X5)
        | ~ l3_lattices(X5)
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) )
      & ( l3_lattices(k7_filter_1(X5,X6))
        | v2_struct_0(X5)
        | ~ l3_lattices(X5)
        | v2_struct_0(X6)
        | ~ l3_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_filter_1])])])])).

fof(c_0_10,plain,(
    ! [X7,X8] :
      ( ( ~ v2_struct_0(k7_filter_1(X7,X8))
        | v2_struct_0(X7)
        | ~ l3_lattices(X7)
        | v2_struct_0(X8)
        | ~ l3_lattices(X8) )
      & ( v3_lattices(k7_filter_1(X7,X8))
        | v2_struct_0(X7)
        | ~ l3_lattices(X7)
        | v2_struct_0(X8)
        | ~ l3_lattices(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_filter_1])])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v10_lattices(X2)
              & l3_lattices(X2) )
           => ( ( v15_lattices(X1)
                & v15_lattices(X2) )
            <=> v15_lattices(k7_filter_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t42_filter_1])).

fof(c_0_12,plain,(
    ! [X9,X10] :
      ( ( ~ v13_lattices(X9)
        | ~ v13_lattices(X10)
        | v13_lattices(k7_filter_1(X9,X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v13_lattices(X9)
        | ~ v13_lattices(k7_filter_1(X9,X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v13_lattices(X10)
        | ~ v13_lattices(k7_filter_1(X9,X10))
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_filter_1])])])])])).

cnf(c_0_13,plain,
    ( v14_lattices(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v14_lattices(k7_filter_1(X2,X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( v14_lattices(X1)
    | v2_struct_0(X1)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( l3_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k7_filter_1(X1,X2))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v10_lattices(esk2_0)
    & l3_lattices(esk2_0)
    & ( ~ v15_lattices(esk1_0)
      | ~ v15_lattices(esk2_0)
      | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) )
    & ( v15_lattices(esk1_0)
      | v15_lattices(k7_filter_1(esk1_0,esk2_0)) )
    & ( v15_lattices(esk2_0)
      | v15_lattices(k7_filter_1(esk1_0,esk2_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).

cnf(c_0_18,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v13_lattices(k7_filter_1(X2,X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_20,plain,(
    ! [X3] :
      ( ( ~ v2_struct_0(X3)
        | v2_struct_0(X3)
        | ~ v13_lattices(X3)
        | ~ v14_lattices(X3)
        | ~ l3_lattices(X3) )
      & ( v15_lattices(X3)
        | v2_struct_0(X3)
        | ~ v13_lattices(X3)
        | ~ v14_lattices(X3)
        | ~ l3_lattices(X3) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc3_lattices])])])])).

cnf(c_0_21,plain,
    ( v14_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v15_lattices(k7_filter_1(X2,X1))
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v15_lattices(esk2_0)
    | v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v15_lattices(k7_filter_1(X2,X1))
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_15]),c_0_16])).

cnf(c_0_30,plain,
    ( v14_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v14_lattices(k7_filter_1(X1,X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v13_lattices(k7_filter_1(X1,X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,plain,
    ( v15_lattices(X1)
    | v2_struct_0(X1)
    | ~ v13_lattices(X1)
    | ~ v14_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( v15_lattices(esk2_0)
    | v14_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27]),c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v15_lattices(esk2_0)
    | v13_lattices(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27]),c_0_28])).

cnf(c_0_35,plain,
    ( v14_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v15_lattices(k7_filter_1(X1,X2))
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( v15_lattices(esk1_0)
    | v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v15_lattices(k7_filter_1(X1,X2))
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_19]),c_0_15]),c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( ~ v15_lattices(esk1_0)
    | ~ v15_lattices(esk2_0)
    | ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( v15_lattices(esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_26])]),c_0_28]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( v15_lattices(esk1_0)
    | v14_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_24]),c_0_23]),c_0_26]),c_0_25])]),c_0_28]),c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( v15_lattices(esk1_0)
    | v13_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_36]),c_0_24]),c_0_23]),c_0_26]),c_0_25])]),c_0_28]),c_0_27])).

cnf(c_0_42,plain,
    ( v14_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v14_lattices(X1)
    | ~ v14_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_43,negated_conjecture,
    ( ~ v15_lattices(k7_filter_1(esk1_0,esk2_0))
    | ~ v15_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_44,negated_conjecture,
    ( v15_lattices(esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_40]),c_0_25])]),c_0_27]),c_0_41])).

cnf(c_0_45,plain,
    ( v15_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v14_lattices(X2)
    | ~ v14_lattices(X1)
    | ~ v13_lattices(k7_filter_1(X1,X2))
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_42]),c_0_15]),c_0_16])).

cnf(c_0_46,plain,
    ( v13_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v13_lattices(X1)
    | ~ v13_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_47,negated_conjecture,
    ( ~ v15_lattices(k7_filter_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_48,plain,
    ( v15_lattices(k7_filter_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v10_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ v14_lattices(X2)
    | ~ v14_lattices(X1)
    | ~ v13_lattices(X2)
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( ~ v14_lattices(esk2_0)
    | ~ v14_lattices(esk1_0)
    | ~ v13_lattices(esk2_0)
    | ~ v13_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_24]),c_0_23]),c_0_26]),c_0_25])]),c_0_27]),c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( ~ v14_lattices(esk1_0)
    | ~ v13_lattices(esk2_0)
    | ~ v13_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_14]),c_0_39]),c_0_26])]),c_0_28])).

cnf(c_0_51,negated_conjecture,
    ( ~ v13_lattices(esk2_0)
    | ~ v13_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_14]),c_0_44]),c_0_25])]),c_0_27])).

cnf(c_0_52,negated_conjecture,
    ( ~ v13_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_19]),c_0_39]),c_0_26])]),c_0_28])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_19]),c_0_44]),c_0_25])]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:00:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___008_C45_F1_PI_S5PRR_SE_Q4_CS_SP_S4S
% 0.14/0.37  # and selection function SelectNewComplexAHPNS.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.026 s
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t41_filter_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>((v14_lattices(X1)&v14_lattices(X2))<=>v14_lattices(k7_filter_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_filter_1)).
% 0.14/0.37  fof(cc4_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v15_lattices(X1))=>((~(v2_struct_0(X1))&v13_lattices(X1))&v14_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_lattices)).
% 0.14/0.37  fof(dt_k7_filter_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&l3_lattices(X1))&~(v2_struct_0(X2)))&l3_lattices(X2))=>(v3_lattices(k7_filter_1(X1,X2))&l3_lattices(k7_filter_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_filter_1)).
% 0.14/0.37  fof(fc2_filter_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&l3_lattices(X1))&~(v2_struct_0(X2)))&l3_lattices(X2))=>(~(v2_struct_0(k7_filter_1(X1,X2)))&v3_lattices(k7_filter_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_filter_1)).
% 0.14/0.37  fof(t42_filter_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>((v15_lattices(X1)&v15_lattices(X2))<=>v15_lattices(k7_filter_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_filter_1)).
% 0.14/0.37  fof(t40_filter_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>((v13_lattices(X1)&v13_lattices(X2))<=>v13_lattices(k7_filter_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_filter_1)).
% 0.14/0.37  fof(cc3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(((~(v2_struct_0(X1))&v13_lattices(X1))&v14_lattices(X1))=>(~(v2_struct_0(X1))&v15_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_lattices)).
% 0.14/0.37  fof(c_0_7, plain, ![X11, X12]:((~v14_lattices(X11)|~v14_lattices(X12)|v14_lattices(k7_filter_1(X11,X12))|(v2_struct_0(X12)|~v10_lattices(X12)|~l3_lattices(X12))|(v2_struct_0(X11)|~v10_lattices(X11)|~l3_lattices(X11)))&((v14_lattices(X11)|~v14_lattices(k7_filter_1(X11,X12))|(v2_struct_0(X12)|~v10_lattices(X12)|~l3_lattices(X12))|(v2_struct_0(X11)|~v10_lattices(X11)|~l3_lattices(X11)))&(v14_lattices(X12)|~v14_lattices(k7_filter_1(X11,X12))|(v2_struct_0(X12)|~v10_lattices(X12)|~l3_lattices(X12))|(v2_struct_0(X11)|~v10_lattices(X11)|~l3_lattices(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_filter_1])])])])])).
% 0.14/0.37  fof(c_0_8, plain, ![X4]:(((~v2_struct_0(X4)|(v2_struct_0(X4)|~v15_lattices(X4))|~l3_lattices(X4))&(v13_lattices(X4)|(v2_struct_0(X4)|~v15_lattices(X4))|~l3_lattices(X4)))&(v14_lattices(X4)|(v2_struct_0(X4)|~v15_lattices(X4))|~l3_lattices(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_lattices])])])])).
% 0.14/0.37  fof(c_0_9, plain, ![X5, X6]:((v3_lattices(k7_filter_1(X5,X6))|(v2_struct_0(X5)|~l3_lattices(X5)|v2_struct_0(X6)|~l3_lattices(X6)))&(l3_lattices(k7_filter_1(X5,X6))|(v2_struct_0(X5)|~l3_lattices(X5)|v2_struct_0(X6)|~l3_lattices(X6)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_filter_1])])])])).
% 0.14/0.37  fof(c_0_10, plain, ![X7, X8]:((~v2_struct_0(k7_filter_1(X7,X8))|(v2_struct_0(X7)|~l3_lattices(X7)|v2_struct_0(X8)|~l3_lattices(X8)))&(v3_lattices(k7_filter_1(X7,X8))|(v2_struct_0(X7)|~l3_lattices(X7)|v2_struct_0(X8)|~l3_lattices(X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_filter_1])])])])).
% 0.14/0.37  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>((v15_lattices(X1)&v15_lattices(X2))<=>v15_lattices(k7_filter_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t42_filter_1])).
% 0.14/0.37  fof(c_0_12, plain, ![X9, X10]:((~v13_lattices(X9)|~v13_lattices(X10)|v13_lattices(k7_filter_1(X9,X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~l3_lattices(X10))|(v2_struct_0(X9)|~v10_lattices(X9)|~l3_lattices(X9)))&((v13_lattices(X9)|~v13_lattices(k7_filter_1(X9,X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~l3_lattices(X10))|(v2_struct_0(X9)|~v10_lattices(X9)|~l3_lattices(X9)))&(v13_lattices(X10)|~v13_lattices(k7_filter_1(X9,X10))|(v2_struct_0(X10)|~v10_lattices(X10)|~l3_lattices(X10))|(v2_struct_0(X9)|~v10_lattices(X9)|~l3_lattices(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_filter_1])])])])])).
% 0.14/0.37  cnf(c_0_13, plain, (v14_lattices(X1)|v2_struct_0(X1)|v2_struct_0(X2)|~v14_lattices(k7_filter_1(X2,X1))|~v10_lattices(X1)|~l3_lattices(X1)|~v10_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_14, plain, (v14_lattices(X1)|v2_struct_0(X1)|~v15_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_15, plain, (l3_lattices(k7_filter_1(X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|~l3_lattices(X1)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_16, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v2_struct_0(k7_filter_1(X1,X2))|~l3_lattices(X1)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  fof(c_0_17, negated_conjecture, (((~v2_struct_0(esk1_0)&v10_lattices(esk1_0))&l3_lattices(esk1_0))&(((~v2_struct_0(esk2_0)&v10_lattices(esk2_0))&l3_lattices(esk2_0))&((~v15_lattices(esk1_0)|~v15_lattices(esk2_0)|~v15_lattices(k7_filter_1(esk1_0,esk2_0)))&((v15_lattices(esk1_0)|v15_lattices(k7_filter_1(esk1_0,esk2_0)))&(v15_lattices(esk2_0)|v15_lattices(k7_filter_1(esk1_0,esk2_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).
% 0.14/0.37  cnf(c_0_18, plain, (v13_lattices(X1)|v2_struct_0(X1)|v2_struct_0(X2)|~v13_lattices(k7_filter_1(X2,X1))|~v10_lattices(X1)|~l3_lattices(X1)|~v10_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_19, plain, (v13_lattices(X1)|v2_struct_0(X1)|~v15_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  fof(c_0_20, plain, ![X3]:((~v2_struct_0(X3)|(v2_struct_0(X3)|~v13_lattices(X3)|~v14_lattices(X3))|~l3_lattices(X3))&(v15_lattices(X3)|(v2_struct_0(X3)|~v13_lattices(X3)|~v14_lattices(X3))|~l3_lattices(X3))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc3_lattices])])])])).
% 0.14/0.37  cnf(c_0_21, plain, (v14_lattices(X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v10_lattices(X2)|~v10_lattices(X1)|~v15_lattices(k7_filter_1(X2,X1))|~l3_lattices(X2)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])).
% 0.14/0.37  cnf(c_0_22, negated_conjecture, (v15_lattices(esk2_0)|v15_lattices(k7_filter_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_23, negated_conjecture, (v10_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_24, negated_conjecture, (v10_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_25, negated_conjecture, (l3_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_26, negated_conjecture, (l3_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_29, plain, (v13_lattices(X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v10_lattices(X2)|~v10_lattices(X1)|~v15_lattices(k7_filter_1(X2,X1))|~l3_lattices(X2)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_15]), c_0_16])).
% 0.14/0.37  cnf(c_0_30, plain, (v14_lattices(X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v14_lattices(k7_filter_1(X1,X2))|~v10_lattices(X2)|~l3_lattices(X2)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_31, plain, (v13_lattices(X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v13_lattices(k7_filter_1(X1,X2))|~v10_lattices(X2)|~l3_lattices(X2)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_32, plain, (v15_lattices(X1)|v2_struct_0(X1)|~v13_lattices(X1)|~v14_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.37  cnf(c_0_33, negated_conjecture, (v15_lattices(esk2_0)|v14_lattices(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])]), c_0_27]), c_0_28])).
% 0.14/0.37  cnf(c_0_34, negated_conjecture, (v15_lattices(esk2_0)|v13_lattices(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])]), c_0_27]), c_0_28])).
% 0.14/0.37  cnf(c_0_35, plain, (v14_lattices(X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v10_lattices(X2)|~v10_lattices(X1)|~v15_lattices(k7_filter_1(X1,X2))|~l3_lattices(X2)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_14]), c_0_15]), c_0_16])).
% 0.14/0.37  cnf(c_0_36, negated_conjecture, (v15_lattices(esk1_0)|v15_lattices(k7_filter_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_37, plain, (v13_lattices(X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v10_lattices(X2)|~v10_lattices(X1)|~v15_lattices(k7_filter_1(X1,X2))|~l3_lattices(X2)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_19]), c_0_15]), c_0_16])).
% 0.14/0.37  cnf(c_0_38, negated_conjecture, (~v15_lattices(esk1_0)|~v15_lattices(esk2_0)|~v15_lattices(k7_filter_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  cnf(c_0_39, negated_conjecture, (v15_lattices(esk2_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_26])]), c_0_28]), c_0_34])).
% 0.14/0.37  cnf(c_0_40, negated_conjecture, (v15_lattices(esk1_0)|v14_lattices(esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_24]), c_0_23]), c_0_26]), c_0_25])]), c_0_28]), c_0_27])).
% 0.14/0.37  cnf(c_0_41, negated_conjecture, (v15_lattices(esk1_0)|v13_lattices(esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_36]), c_0_24]), c_0_23]), c_0_26]), c_0_25])]), c_0_28]), c_0_27])).
% 0.14/0.37  cnf(c_0_42, plain, (v14_lattices(k7_filter_1(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v14_lattices(X1)|~v14_lattices(X2)|~v10_lattices(X2)|~l3_lattices(X2)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_43, negated_conjecture, (~v15_lattices(k7_filter_1(esk1_0,esk2_0))|~v15_lattices(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39])])).
% 0.14/0.37  cnf(c_0_44, negated_conjecture, (v15_lattices(esk1_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_40]), c_0_25])]), c_0_27]), c_0_41])).
% 0.14/0.37  cnf(c_0_45, plain, (v15_lattices(k7_filter_1(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v10_lattices(X2)|~v10_lattices(X1)|~v14_lattices(X2)|~v14_lattices(X1)|~v13_lattices(k7_filter_1(X1,X2))|~l3_lattices(X2)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_42]), c_0_15]), c_0_16])).
% 0.14/0.37  cnf(c_0_46, plain, (v13_lattices(k7_filter_1(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v13_lattices(X1)|~v13_lattices(X2)|~v10_lattices(X2)|~l3_lattices(X2)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_47, negated_conjecture, (~v15_lattices(k7_filter_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 0.14/0.37  cnf(c_0_48, plain, (v15_lattices(k7_filter_1(X1,X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v10_lattices(X2)|~v10_lattices(X1)|~v14_lattices(X2)|~v14_lattices(X1)|~v13_lattices(X2)|~v13_lattices(X1)|~l3_lattices(X2)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.14/0.37  cnf(c_0_49, negated_conjecture, (~v14_lattices(esk2_0)|~v14_lattices(esk1_0)|~v13_lattices(esk2_0)|~v13_lattices(esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_24]), c_0_23]), c_0_26]), c_0_25])]), c_0_27]), c_0_28])).
% 0.14/0.37  cnf(c_0_50, negated_conjecture, (~v14_lattices(esk1_0)|~v13_lattices(esk2_0)|~v13_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_14]), c_0_39]), c_0_26])]), c_0_28])).
% 0.14/0.37  cnf(c_0_51, negated_conjecture, (~v13_lattices(esk2_0)|~v13_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_14]), c_0_44]), c_0_25])]), c_0_27])).
% 0.14/0.37  cnf(c_0_52, negated_conjecture, (~v13_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_19]), c_0_39]), c_0_26])]), c_0_28])).
% 0.14/0.37  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_19]), c_0_44]), c_0_25])]), c_0_27]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 54
% 0.14/0.37  # Proof object clause steps            : 39
% 0.14/0.37  # Proof object formula steps           : 15
% 0.14/0.37  # Proof object conjectures             : 25
% 0.14/0.37  # Proof object clause conjectures      : 22
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 20
% 0.14/0.37  # Proof object initial formulas used   : 7
% 0.14/0.37  # Proof object generating inferences   : 17
% 0.14/0.37  # Proof object simplifying inferences  : 73
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 7
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 24
% 0.14/0.37  # Removed in clause preprocessing      : 2
% 0.14/0.37  # Initial clauses in saturation        : 22
% 0.14/0.37  # Processed clauses                    : 44
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 1
% 0.14/0.37  # ...remaining for further processing  : 43
% 0.14/0.37  # Other redundant clauses eliminated   : 0
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 2
% 0.14/0.37  # Backward-rewritten                   : 12
% 0.14/0.37  # Generated clauses                    : 33
% 0.14/0.37  # ...of the previous two non-trivial   : 23
% 0.14/0.37  # Contextual simplify-reflections      : 13
% 0.14/0.37  # Paramodulations                      : 33
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 0
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 29
% 0.14/0.37  #    Positive orientable unit clauses  : 6
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 4
% 0.14/0.37  #    Non-unit-clauses                  : 19
% 0.14/0.37  # Current number of unprocessed clauses: 0
% 0.14/0.37  # ...number of literals in the above   : 0
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 14
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 352
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 102
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 16
% 0.14/0.37  # Unit Clause-clause subsumption calls : 4
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 2
% 0.14/0.37  # BW rewrite match successes           : 2
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 2955
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.027 s
% 0.14/0.37  # System time              : 0.005 s
% 0.14/0.37  # Total time               : 0.032 s
% 0.14/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
