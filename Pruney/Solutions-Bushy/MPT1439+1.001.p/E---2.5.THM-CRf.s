%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1439+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:16 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 136 expanded)
%              Number of clauses        :   23 (  41 expanded)
%              Number of leaves         :    4 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :  131 (1162 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_filter_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v10_lattices(X3)
                & l3_lattices(X3) )
             => ( ( r1_filter_1(X1,X2)
                  & r1_filter_1(X2,X3) )
               => r1_filter_1(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_filter_1)).

fof(d9_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => ( r1_filter_1(X1,X2)
          <=> r4_wellord1(k8_filter_1(X1),k8_filter_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_filter_1)).

fof(dt_k8_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => v1_relat_1(k8_filter_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_filter_1)).

fof(t52_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X2,X3) )
               => r4_wellord1(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_wellord1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v10_lattices(X2)
              & l3_lattices(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & v10_lattices(X3)
                  & l3_lattices(X3) )
               => ( ( r1_filter_1(X1,X2)
                    & r1_filter_1(X2,X3) )
                 => r1_filter_1(X1,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_filter_1])).

fof(c_0_5,plain,(
    ! [X4,X5] :
      ( ( ~ r1_filter_1(X4,X5)
        | r4_wellord1(k8_filter_1(X4),k8_filter_1(X5))
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( ~ r4_wellord1(k8_filter_1(X4),k8_filter_1(X5))
        | r1_filter_1(X4,X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_filter_1])])])])])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v10_lattices(esk2_0)
    & l3_lattices(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v10_lattices(esk3_0)
    & l3_lattices(esk3_0)
    & r1_filter_1(esk1_0,esk2_0)
    & r1_filter_1(esk2_0,esk3_0)
    & ~ r1_filter_1(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X6] :
      ( v2_struct_0(X6)
      | ~ v10_lattices(X6)
      | ~ l3_lattices(X6)
      | v1_relat_1(k8_filter_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_filter_1])])])).

fof(c_0_8,plain,(
    ! [X7,X8,X9] :
      ( ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | ~ r4_wellord1(X7,X8)
      | ~ r4_wellord1(X8,X9)
      | r4_wellord1(X7,X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_wellord1])])])).

cnf(c_0_9,plain,
    ( r4_wellord1(k8_filter_1(X1),k8_filter_1(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_filter_1(X1,X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( r1_filter_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( l3_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( v10_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | v1_relat_1(k8_filter_1(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( r4_wellord1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r4_wellord1(X1,X2)
    | ~ r4_wellord1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( r4_wellord1(k8_filter_1(esk2_0),k8_filter_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(k8_filter_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_11]),c_0_13])]),c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(k8_filter_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_12]),c_0_14])]),c_0_16])).

cnf(c_0_22,plain,
    ( r1_filter_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r4_wellord1(k8_filter_1(X1),k8_filter_1(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,negated_conjecture,
    ( r4_wellord1(X1,k8_filter_1(esk3_0))
    | ~ v1_relat_1(X1)
    | ~ r4_wellord1(X1,k8_filter_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_24,negated_conjecture,
    ( r1_filter_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_28,negated_conjecture,
    ( r1_filter_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ r4_wellord1(k8_filter_1(X1),k8_filter_1(esk2_0))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_11]),c_0_13])]),c_0_15]),c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( r4_wellord1(k8_filter_1(esk1_0),k8_filter_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_24]),c_0_12]),c_0_25]),c_0_14]),c_0_26])]),c_0_16]),c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_filter_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_25]),c_0_26])]),c_0_30]),c_0_27]),
    [proof]).

%------------------------------------------------------------------------------
