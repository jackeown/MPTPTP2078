%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:51 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 325 expanded)
%              Number of clauses        :   41 ( 103 expanded)
%              Number of leaves         :    7 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :  267 (2181 expanded)
%              Number of equality atoms :   27 ( 367 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_filter_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( k2_filter_0(X1,X2) = k2_filter_0(X1,X3)
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_filter_1)).

fof(t17_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k1_lattices(X1,X2,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( k2_filter_0(X1,X2) = k2_filter_0(X1,X3)
                 => X2 = X3 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t2_filter_1])).

fof(c_0_8,plain,(
    ! [X12,X13] :
      ( v2_struct_0(X12)
      | ~ v6_lattices(X12)
      | ~ v8_lattices(X12)
      | ~ v9_lattices(X12)
      | ~ l3_lattices(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | k1_lattices(X12,X13,X13) = X13 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_lattices])])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & k2_filter_0(esk1_0,esk2_0) = k2_filter_0(esk1_0,esk3_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

cnf(c_0_10,plain,
    ( v2_struct_0(X1)
    | k1_lattices(X1,X2,X2) = X2
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

fof(c_0_14,plain,(
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

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,esk2_0) = esk2_0
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_17,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( k1_lattices(esk1_0,esk3_0,esk3_0) = esk3_0
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_15]),c_0_12])]),c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,esk2_0) = esk2_0
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_12])]),c_0_13])).

cnf(c_0_21,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( k1_lattices(esk1_0,esk3_0,esk3_0) = esk3_0
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_17]),c_0_18]),c_0_12])]),c_0_13])).

fof(c_0_23,plain,(
    ! [X5,X6,X7] :
      ( ( ~ r1_lattices(X5,X6,X7)
        | k1_lattices(X5,X6,X7) = X7
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l2_lattices(X5) )
      & ( k1_lattices(X5,X6,X7) != X7
        | r1_lattices(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l2_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

cnf(c_0_24,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,esk2_0) = esk2_0
    | ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_18]),c_0_12])]),c_0_13])).

cnf(c_0_25,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( k1_lattices(esk1_0,esk3_0,esk3_0) = esk3_0
    | ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_21]),c_0_18]),c_0_12])]),c_0_13])).

cnf(c_0_27,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,esk2_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_18]),c_0_12])]),c_0_13]),
    [final]).

fof(c_0_29,plain,(
    ! [X8] :
      ( ( l1_lattices(X8)
        | ~ l3_lattices(X8) )
      & ( l2_lattices(X8)
        | ~ l3_lattices(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_30,negated_conjecture,
    ( k1_lattices(esk1_0,esk3_0,esk3_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_25]),c_0_18]),c_0_12])]),c_0_13]),
    [final]).

fof(c_0_31,plain,(
    ! [X9,X10,X11] :
      ( ( ~ r3_lattices(X9,X10,X11)
        | r1_lattices(X9,X10,X11)
        | v2_struct_0(X9)
        | ~ v6_lattices(X9)
        | ~ v8_lattices(X9)
        | ~ v9_lattices(X9)
        | ~ l3_lattices(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9)) )
      & ( ~ r1_lattices(X9,X10,X11)
        | r3_lattices(X9,X10,X11)
        | v2_struct_0(X9)
        | ~ v6_lattices(X9)
        | ~ v8_lattices(X9)
        | ~ v9_lattices(X9)
        | ~ l3_lattices(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_32,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,esk2_0)
    | ~ l2_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_11])]),c_0_13])).

cnf(c_0_33,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( r1_lattices(esk1_0,esk3_0,esk3_0)
    | ~ l2_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_30]),c_0_15])]),c_0_13])).

cnf(c_0_35,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_12])]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( r1_lattices(esk1_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_12])]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk2_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( r3_lattices(esk1_0,esk3_0,esk3_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_37]),c_0_15]),c_0_12])]),c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk2_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_17]),c_0_18]),c_0_12])]),c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( r3_lattices(esk1_0,esk3_0,esk3_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_17]),c_0_18]),c_0_12])]),c_0_13])).

fof(c_0_42,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ v4_lattices(X14)
      | ~ l2_lattices(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | ~ r1_lattices(X14,X15,X16)
      | ~ r1_lattices(X14,X16,X15)
      | X15 = X16 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

cnf(c_0_43,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk2_0)
    | ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_21]),c_0_18]),c_0_12])]),c_0_13])).

cnf(c_0_44,negated_conjecture,
    ( r3_lattices(esk1_0,esk3_0,esk3_0)
    | ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_21]),c_0_18]),c_0_12])]),c_0_13])).

cnf(c_0_45,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42]),
    [final]).

cnf(c_0_47,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_48,plain,
    ( v7_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_49,plain,
    ( v5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_50,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_51,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_25]),c_0_18]),c_0_12])]),c_0_13]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( r3_lattices(esk1_0,esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_25]),c_0_18]),c_0_12])]),c_0_13]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( k2_filter_0(esk1_0,esk2_0) = k2_filter_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:01:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.12/0.38  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.028 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # No proof found!
% 0.12/0.38  # SZS status CounterSatisfiable
% 0.12/0.38  # SZS output start Saturation
% 0.12/0.38  fof(t2_filter_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_filter_0(X1,X2)=k2_filter_0(X1,X3)=>X2=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_filter_1)).
% 0.12/0.38  fof(t17_lattices, axiom, ![X1]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k1_lattices(X1,X2,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_lattices)).
% 0.12/0.38  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.12/0.38  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 0.12/0.38  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.12/0.38  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.12/0.38  fof(t26_lattices, axiom, ![X1]:(((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_lattices(X1,X2,X3)&r1_lattices(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_lattices)).
% 0.12/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_filter_0(X1,X2)=k2_filter_0(X1,X3)=>X2=X3))))), inference(assume_negation,[status(cth)],[t2_filter_1])).
% 0.12/0.38  fof(c_0_8, plain, ![X12, X13]:(v2_struct_0(X12)|~v6_lattices(X12)|~v8_lattices(X12)|~v9_lattices(X12)|~l3_lattices(X12)|(~m1_subset_1(X13,u1_struct_0(X12))|k1_lattices(X12,X13,X13)=X13)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_lattices])])])])).
% 0.12/0.38  fof(c_0_9, negated_conjecture, (((~v2_struct_0(esk1_0)&v10_lattices(esk1_0))&l3_lattices(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(m1_subset_1(esk3_0,u1_struct_0(esk1_0))&(k2_filter_0(esk1_0,esk2_0)=k2_filter_0(esk1_0,esk3_0)&esk2_0!=esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.12/0.38  cnf(c_0_10, plain, (v2_struct_0(X1)|k1_lattices(X1,X2,X2)=X2|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.12/0.38  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.12/0.38  cnf(c_0_12, negated_conjecture, (l3_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.12/0.38  cnf(c_0_13, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.12/0.38  fof(c_0_14, plain, ![X4]:(((((((~v2_struct_0(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))&(v4_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v5_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v6_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v7_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v8_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v9_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.12/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.12/0.38  cnf(c_0_16, negated_conjecture, (k1_lattices(esk1_0,esk2_0,esk2_0)=esk2_0|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)|~v6_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])]), c_0_13])).
% 0.12/0.38  cnf(c_0_17, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (v10_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (k1_lattices(esk1_0,esk3_0,esk3_0)=esk3_0|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)|~v6_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_15]), c_0_12])]), c_0_13])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (k1_lattices(esk1_0,esk2_0,esk2_0)=esk2_0|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_12])]), c_0_13])).
% 0.12/0.38  cnf(c_0_21, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.12/0.38  cnf(c_0_22, negated_conjecture, (k1_lattices(esk1_0,esk3_0,esk3_0)=esk3_0|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_17]), c_0_18]), c_0_12])]), c_0_13])).
% 0.12/0.38  fof(c_0_23, plain, ![X5, X6, X7]:((~r1_lattices(X5,X6,X7)|k1_lattices(X5,X6,X7)=X7|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l2_lattices(X5)))&(k1_lattices(X5,X6,X7)!=X7|r1_lattices(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l2_lattices(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (k1_lattices(esk1_0,esk2_0,esk2_0)=esk2_0|~v9_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_18]), c_0_12])]), c_0_13])).
% 0.12/0.38  cnf(c_0_25, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (k1_lattices(esk1_0,esk3_0,esk3_0)=esk3_0|~v9_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_21]), c_0_18]), c_0_12])]), c_0_13])).
% 0.12/0.38  cnf(c_0_27, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k1_lattices(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.12/0.38  cnf(c_0_28, negated_conjecture, (k1_lattices(esk1_0,esk2_0,esk2_0)=esk2_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_18]), c_0_12])]), c_0_13]), ['final']).
% 0.12/0.38  fof(c_0_29, plain, ![X8]:((l1_lattices(X8)|~l3_lattices(X8))&(l2_lattices(X8)|~l3_lattices(X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (k1_lattices(esk1_0,esk3_0,esk3_0)=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_25]), c_0_18]), c_0_12])]), c_0_13]), ['final']).
% 0.12/0.38  fof(c_0_31, plain, ![X9, X10, X11]:((~r3_lattices(X9,X10,X11)|r1_lattices(X9,X10,X11)|(v2_struct_0(X9)|~v6_lattices(X9)|~v8_lattices(X9)|~v9_lattices(X9)|~l3_lattices(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))&(~r1_lattices(X9,X10,X11)|r3_lattices(X9,X10,X11)|(v2_struct_0(X9)|~v6_lattices(X9)|~v8_lattices(X9)|~v9_lattices(X9)|~l3_lattices(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~m1_subset_1(X11,u1_struct_0(X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (r1_lattices(esk1_0,esk2_0,esk2_0)|~l2_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_11])]), c_0_13])).
% 0.12/0.38  cnf(c_0_33, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (r1_lattices(esk1_0,esk3_0,esk3_0)|~l2_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_30]), c_0_15])]), c_0_13])).
% 0.12/0.38  cnf(c_0_35, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.12/0.38  cnf(c_0_36, negated_conjecture, (r1_lattices(esk1_0,esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_12])]), ['final']).
% 0.12/0.38  cnf(c_0_37, negated_conjecture, (r1_lattices(esk1_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_12])]), ['final']).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (r3_lattices(esk1_0,esk2_0,esk2_0)|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)|~v6_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_11]), c_0_12])]), c_0_13])).
% 0.12/0.38  cnf(c_0_39, negated_conjecture, (r3_lattices(esk1_0,esk3_0,esk3_0)|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)|~v6_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_37]), c_0_15]), c_0_12])]), c_0_13])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (r3_lattices(esk1_0,esk2_0,esk2_0)|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_17]), c_0_18]), c_0_12])]), c_0_13])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (r3_lattices(esk1_0,esk3_0,esk3_0)|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_17]), c_0_18]), c_0_12])]), c_0_13])).
% 0.12/0.38  fof(c_0_42, plain, ![X14, X15, X16]:(v2_struct_0(X14)|~v4_lattices(X14)|~l2_lattices(X14)|(~m1_subset_1(X15,u1_struct_0(X14))|(~m1_subset_1(X16,u1_struct_0(X14))|(~r1_lattices(X14,X15,X16)|~r1_lattices(X14,X16,X15)|X15=X16)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, (r3_lattices(esk1_0,esk2_0,esk2_0)|~v9_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_21]), c_0_18]), c_0_12])]), c_0_13])).
% 0.12/0.38  cnf(c_0_44, negated_conjecture, (r3_lattices(esk1_0,esk3_0,esk3_0)|~v9_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_21]), c_0_18]), c_0_12])]), c_0_13])).
% 0.12/0.38  cnf(c_0_45, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.12/0.38  cnf(c_0_46, plain, (v2_struct_0(X1)|X2=X3|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattices(X1,X2,X3)|~r1_lattices(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_42]), ['final']).
% 0.12/0.38  cnf(c_0_47, plain, (k1_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.12/0.38  cnf(c_0_48, plain, (v7_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.12/0.38  cnf(c_0_49, plain, (v5_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.12/0.38  cnf(c_0_50, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.12/0.38  cnf(c_0_51, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.12/0.38  cnf(c_0_53, negated_conjecture, (r3_lattices(esk1_0,esk2_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_25]), c_0_18]), c_0_12])]), c_0_13]), ['final']).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, (r3_lattices(esk1_0,esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_25]), c_0_18]), c_0_12])]), c_0_13]), ['final']).
% 0.12/0.38  cnf(c_0_55, negated_conjecture, (k2_filter_0(esk1_0,esk2_0)=k2_filter_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.12/0.38  # SZS output end Saturation
% 0.12/0.38  # Proof object total steps             : 56
% 0.12/0.38  # Proof object clause steps            : 41
% 0.12/0.38  # Proof object formula steps           : 15
% 0.12/0.38  # Proof object conjectures             : 30
% 0.12/0.38  # Proof object clause conjectures      : 27
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 21
% 0.12/0.38  # Proof object initial formulas used   : 7
% 0.12/0.38  # Proof object generating inferences   : 20
% 0.12/0.38  # Proof object simplifying inferences  : 72
% 0.12/0.38  # Parsed axioms                        : 7
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 22
% 0.12/0.38  # Removed in clause preprocessing      : 1
% 0.12/0.38  # Initial clauses in saturation        : 21
% 0.12/0.38  # Processed clauses                    : 62
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 0
% 0.12/0.38  # ...remaining for further processing  : 62
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 8
% 0.12/0.38  # Backward-rewritten                   : 6
% 0.12/0.38  # Generated clauses                    : 24
% 0.12/0.38  # ...of the previous two non-trivial   : 20
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 24
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 27
% 0.12/0.38  #    Positive orientable unit clauses  : 11
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 2
% 0.12/0.38  #    Non-unit-clauses                  : 14
% 0.12/0.38  # Current number of unprocessed clauses: 0
% 0.12/0.38  # ...number of literals in the above   : 0
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 35
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 358
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 152
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 8
% 0.12/0.38  # Unit Clause-clause subsumption calls : 0
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 6
% 0.12/0.38  # BW rewrite match successes           : 6
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 2596
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.031 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.034 s
% 0.12/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
