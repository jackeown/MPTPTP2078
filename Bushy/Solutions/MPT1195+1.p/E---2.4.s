%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattices__t21_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:00 EDT 2019

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 160 expanded)
%              Number of clauses        :   22 (  52 expanded)
%              Number of leaves         :    5 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  153 (1030 expanded)
%              Number of equality atoms :   27 ( 161 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_lattices,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',t21_lattices)).

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
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',d3_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',dt_l3_lattices)).

fof(d9_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v9_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',d9_lattices)).

fof(d8_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v8_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t21_lattices.p',d8_lattices)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t21_lattices])).

fof(c_0_6,plain,(
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

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v8_lattices(esk1_0)
    & v9_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & ( ~ r1_lattices(esk1_0,esk2_0,esk3_0)
      | k2_lattices(esk1_0,esk2_0,esk3_0) != esk2_0 )
    & ( r1_lattices(esk1_0,esk2_0,esk3_0)
      | k2_lattices(esk1_0,esk2_0,esk3_0) = esk2_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

cnf(c_0_8,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( k1_lattices(esk1_0,X1,esk3_0) = esk3_0
    | ~ l2_lattices(esk1_0)
    | ~ r1_lattices(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])).

cnf(c_0_12,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,esk3_0)
    | k2_lattices(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_14,plain,(
    ! [X35] :
      ( ( l1_lattices(X35)
        | ~ l3_lattices(X35) )
      & ( l2_lattices(X35)
        | ~ l3_lattices(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_15,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v9_lattices(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | k2_lattices(X18,X19,k1_lattices(X18,X19,X20)) = X19
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( m1_subset_1(esk6_1(X18),u1_struct_0(X18))
        | v9_lattices(X18)
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( m1_subset_1(esk7_1(X18),u1_struct_0(X18))
        | v9_lattices(X18)
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( k2_lattices(X18,esk6_1(X18),k1_lattices(X18,esk6_1(X18),esk7_1(X18))) != esk6_1(X18)
        | v9_lattices(X18)
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).

cnf(c_0_16,negated_conjecture,
    ( k2_lattices(esk1_0,esk2_0,esk3_0) = esk2_0
    | k1_lattices(esk1_0,esk2_0,esk3_0) = esk3_0
    | ~ l2_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_17,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,esk3_0) = esk3_0
    | k2_lattices(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_21,negated_conjecture,
    ( v9_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_22,plain,(
    ! [X13,X14,X15] :
      ( ( ~ v8_lattices(X13)
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | k1_lattices(X13,k2_lattices(X13,X14,X15),X15) = X15
        | v2_struct_0(X13)
        | ~ l3_lattices(X13) )
      & ( m1_subset_1(esk4_1(X13),u1_struct_0(X13))
        | v8_lattices(X13)
        | v2_struct_0(X13)
        | ~ l3_lattices(X13) )
      & ( m1_subset_1(esk5_1(X13),u1_struct_0(X13))
        | v8_lattices(X13)
        | v2_struct_0(X13)
        | ~ l3_lattices(X13) )
      & ( k1_lattices(X13,k2_lattices(X13,esk4_1(X13),esk5_1(X13)),esk5_1(X13)) != esk5_1(X13)
        | v8_lattices(X13)
        | v2_struct_0(X13)
        | ~ l3_lattices(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_lattices(esk1_0,esk2_0,esk3_0)
    | k2_lattices(esk1_0,esk2_0,esk3_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( k2_lattices(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_9]),c_0_13]),c_0_18]),c_0_21])]),c_0_10])).

cnf(c_0_25,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v8_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_29,negated_conjecture,
    ( r1_lattices(esk1_0,X1,esk3_0)
    | k1_lattices(esk1_0,X1,esk3_0) != esk3_0
    | ~ l2_lattices(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_9]),c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,esk3_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_24]),c_0_9]),c_0_13]),c_0_18]),c_0_27])]),c_0_10])).

cnf(c_0_31,negated_conjecture,
    ( ~ l2_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_13])]),c_0_30])])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_17]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
