%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattices__t22_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:00 EDT 2019

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 179 expanded)
%              Number of clauses        :   24 (  59 expanded)
%              Number of leaves         :    6 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :  160 (1134 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_lattices(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => r1_lattices(X1,X2,k1_lattices(X1,X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t22_lattices.p',t22_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t22_lattices.p',dt_l3_lattices)).

fof(dt_k1_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k1_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t22_lattices.p',dt_k1_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattices__t22_lattices.p',t17_lattices)).

fof(d5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ( v5_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => k1_lattices(X1,X2,k1_lattices(X1,X3,X4)) = k1_lattices(X1,k1_lattices(X1,X2,X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t22_lattices.p',d5_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattices__t22_lattices.p',d3_lattices)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_lattices(X1)
          & v6_lattices(X1)
          & v8_lattices(X1)
          & v9_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => r1_lattices(X1,X2,k1_lattices(X1,X2,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t22_lattices])).

fof(c_0_7,plain,(
    ! [X29] :
      ( ( l1_lattices(X29)
        | ~ l3_lattices(X29) )
      & ( l2_lattices(X29)
        | ~ l3_lattices(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v5_lattices(esk1_0)
    & v6_lattices(esk1_0)
    & v8_lattices(esk1_0)
    & v9_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & ~ r1_lattices(esk1_0,esk2_0,k1_lattices(esk1_0,esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X20,X21,X22] :
      ( v2_struct_0(X20)
      | ~ l2_lattices(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | ~ m1_subset_1(X22,u1_struct_0(X20))
      | m1_subset_1(k1_lattices(X20,X21,X22),u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_lattices])])])).

cnf(c_0_10,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X41,X42] :
      ( v2_struct_0(X41)
      | ~ v6_lattices(X41)
      | ~ v8_lattices(X41)
      | ~ v9_lattices(X41)
      | ~ l3_lattices(X41)
      | ~ m1_subset_1(X42,u1_struct_0(X41))
      | k1_lattices(X41,X42,X42) = X42 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_lattices])])])])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( l2_lattices(esk1_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_17,plain,(
    ! [X13,X14,X15,X16] :
      ( ( ~ v5_lattices(X13)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X16,u1_struct_0(X13))
        | k1_lattices(X13,X14,k1_lattices(X13,X15,X16)) = k1_lattices(X13,k1_lattices(X13,X14,X15),X16)
        | v2_struct_0(X13)
        | ~ l2_lattices(X13) )
      & ( m1_subset_1(esk4_1(X13),u1_struct_0(X13))
        | v5_lattices(X13)
        | v2_struct_0(X13)
        | ~ l2_lattices(X13) )
      & ( m1_subset_1(esk5_1(X13),u1_struct_0(X13))
        | v5_lattices(X13)
        | v2_struct_0(X13)
        | ~ l2_lattices(X13) )
      & ( m1_subset_1(esk6_1(X13),u1_struct_0(X13))
        | v5_lattices(X13)
        | v2_struct_0(X13)
        | ~ l2_lattices(X13) )
      & ( k1_lattices(X13,esk4_1(X13),k1_lattices(X13,esk5_1(X13),esk6_1(X13))) != k1_lattices(X13,k1_lattices(X13,esk4_1(X13),esk5_1(X13)),esk6_1(X13))
        | v5_lattices(X13)
        | v2_struct_0(X13)
        | ~ l2_lattices(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_lattices])])])])])])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | k1_lattices(X1,X2,X2) = X2
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( v9_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( v8_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( v6_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(k1_lattices(esk1_0,X1,esk3_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_24,plain,
    ( k1_lattices(X1,X2,k1_lattices(X1,X3,X4)) = k1_lattices(X1,k1_lattices(X1,X2,X3),X4)
    | v2_struct_0(X1)
    | ~ v5_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,esk2_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_11]),c_0_20]),c_0_21]),c_0_22])]),c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( v5_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_27,plain,(
    ! [X10,X11,X12] :
      ( ( ~ r1_lattices(X10,X11,X12)
        | k1_lattices(X10,X11,X12) = X12
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ l2_lattices(X10) )
      & ( k1_lattices(X10,X11,X12) != X12
        | r1_lattices(X10,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ l2_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k1_lattices(esk1_0,X1,k1_lattices(esk1_0,X2,esk3_0)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_23]),c_0_16])]),c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,k1_lattices(esk1_0,esk2_0,X1)) = k1_lattices(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_16]),c_0_19]),c_0_26])]),c_0_15])).

cnf(c_0_30,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k1_lattices(esk1_0,esk2_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_19]),c_0_14])])).

cnf(c_0_32,negated_conjecture,
    ( k1_lattices(esk1_0,k1_lattices(esk1_0,X1,X2),esk3_0) = k1_lattices(esk1_0,X1,k1_lattices(esk1_0,X2,esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_14]),c_0_26])]),c_0_15]),c_0_16])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_lattices(esk1_0,esk2_0,k1_lattices(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,negated_conjecture,
    ( r1_lattices(esk1_0,X1,k1_lattices(esk1_0,esk2_0,esk3_0))
    | k1_lattices(esk1_0,X1,k1_lattices(esk1_0,esk2_0,esk3_0)) != k1_lattices(esk1_0,esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_16])]),c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,k1_lattices(esk1_0,esk2_0,esk3_0)) = k1_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_25]),c_0_19])])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
