%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattices__t25_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:01 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   27 ( 129 expanded)
%              Number of clauses        :   20 (  41 expanded)
%              Number of leaves         :    3 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :  119 ( 881 expanded)
%              Number of equality atoms :   16 (  29 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_lattices(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_lattices(X1,X2,X3)
                      & r1_lattices(X1,X3,X4) )
                   => r1_lattices(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t25_lattices.p',t25_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/lattices__t25_lattices.p',d3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/lattices__t25_lattices.p',d5_lattices)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_lattices(X1)
          & l2_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r1_lattices(X1,X2,X3)
                        & r1_lattices(X1,X3,X4) )
                     => r1_lattices(X1,X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_lattices])).

fof(c_0_4,plain,(
    ! [X11,X12,X13] :
      ( ( ~ r1_lattices(X11,X12,X13)
        | k1_lattices(X11,X12,X13) = X13
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l2_lattices(X11) )
      & ( k1_lattices(X11,X12,X13) != X13
        | r1_lattices(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l2_lattices(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

fof(c_0_5,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v5_lattices(esk1_0)
    & l2_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    & r1_lattices(esk1_0,esk2_0,esk3_0)
    & r1_lattices(esk1_0,esk3_0,esk4_0)
    & ~ r1_lattices(esk1_0,esk2_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

fof(c_0_6,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ v5_lattices(X14)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | k1_lattices(X14,X15,k1_lattices(X14,X16,X17)) = k1_lattices(X14,k1_lattices(X14,X15,X16),X17)
        | v2_struct_0(X14)
        | ~ l2_lattices(X14) )
      & ( m1_subset_1(esk5_1(X14),u1_struct_0(X14))
        | v5_lattices(X14)
        | v2_struct_0(X14)
        | ~ l2_lattices(X14) )
      & ( m1_subset_1(esk6_1(X14),u1_struct_0(X14))
        | v5_lattices(X14)
        | v2_struct_0(X14)
        | ~ l2_lattices(X14) )
      & ( m1_subset_1(esk7_1(X14),u1_struct_0(X14))
        | v5_lattices(X14)
        | v2_struct_0(X14)
        | ~ l2_lattices(X14) )
      & ( k1_lattices(X14,esk5_1(X14),k1_lattices(X14,esk6_1(X14),esk7_1(X14))) != k1_lattices(X14,k1_lattices(X14,esk5_1(X14),esk6_1(X14)),esk7_1(X14))
        | v5_lattices(X14)
        | v2_struct_0(X14)
        | ~ l2_lattices(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_lattices])])])])])])).

cnf(c_0_7,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( l2_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,plain,
    ( k1_lattices(X1,X2,k1_lattices(X1,X3,X4)) = k1_lattices(X1,k1_lattices(X1,X2,X3),X4)
    | v2_struct_0(X1)
    | ~ v5_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( v5_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( k1_lattices(esk1_0,X1,esk3_0) = esk3_0
    | ~ r1_lattices(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r1_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( k1_lattices(esk1_0,X1,esk4_0) = esk4_0
    | ~ r1_lattices(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_11]),c_0_9])]),c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( r1_lattices(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_lattices(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( r1_lattices(esk1_0,X1,esk4_0)
    | k1_lattices(esk1_0,X1,esk4_0) != esk4_0
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_11]),c_0_9])]),c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( k1_lattices(esk1_0,k1_lattices(esk1_0,X1,X2),esk4_0) = k1_lattices(esk1_0,X1,k1_lattices(esk1_0,X2,esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_11]),c_0_9]),c_0_14])]),c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_24,negated_conjecture,
    ( k1_lattices(esk1_0,esk3_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_8])])).

cnf(c_0_25,negated_conjecture,
    ( k1_lattices(esk1_0,esk2_0,esk4_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_17])])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_24]),c_0_8]),c_0_17])]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
