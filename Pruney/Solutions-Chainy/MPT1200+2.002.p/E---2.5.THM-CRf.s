%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:23 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 227 expanded)
%              Number of clauses        :   30 (  74 expanded)
%              Number of leaves         :    7 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  224 (1654 expanded)
%              Number of equality atoms :   23 (  35 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   23 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v7_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattices(X1,X2,X3)
                   => r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_lattices)).

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

fof(dt_k2_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).

fof(d7_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v7_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => k2_lattices(X1,X2,k2_lattices(X1,X3,X4)) = k2_lattices(X1,k2_lattices(X1,X2,X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

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

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v7_lattices(X1)
          & v8_lattices(X1)
          & v9_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattices(X1,X2,X3)
                     => r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t27_lattices])).

fof(c_0_8,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r1_lattices(X24,X25,X26)
        | k2_lattices(X24,X25,X26) = X25
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v8_lattices(X24)
        | ~ v9_lattices(X24)
        | ~ l3_lattices(X24) )
      & ( k2_lattices(X24,X25,X26) != X25
        | r1_lattices(X24,X25,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X24))
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ v8_lattices(X24)
        | ~ v9_lattices(X24)
        | ~ l3_lattices(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v7_lattices(esk6_0)
    & v8_lattices(esk6_0)
    & v9_lattices(esk6_0)
    & l3_lattices(esk6_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    & m1_subset_1(esk9_0,u1_struct_0(esk6_0))
    & r1_lattices(esk6_0,esk7_0,esk8_0)
    & ~ r1_lattices(esk6_0,k2_lattices(esk6_0,esk7_0,esk9_0),k2_lattices(esk6_0,esk8_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X20,X21,X22] :
      ( v2_struct_0(X20)
      | ~ l1_lattices(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | ~ m1_subset_1(X22,u1_struct_0(X20))
      | m1_subset_1(k2_lattices(X20,X21,X22),u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattices])])])).

fof(c_0_11,plain,(
    ! [X8,X9,X10,X11] :
      ( ( ~ v7_lattices(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X11,u1_struct_0(X8))
        | k2_lattices(X8,X9,k2_lattices(X8,X10,X11)) = k2_lattices(X8,k2_lattices(X8,X9,X10),X11)
        | v2_struct_0(X8)
        | ~ l1_lattices(X8) )
      & ( m1_subset_1(esk1_1(X8),u1_struct_0(X8))
        | v7_lattices(X8)
        | v2_struct_0(X8)
        | ~ l1_lattices(X8) )
      & ( m1_subset_1(esk2_1(X8),u1_struct_0(X8))
        | v7_lattices(X8)
        | v2_struct_0(X8)
        | ~ l1_lattices(X8) )
      & ( m1_subset_1(esk3_1(X8),u1_struct_0(X8))
        | v7_lattices(X8)
        | v2_struct_0(X8)
        | ~ l1_lattices(X8) )
      & ( k2_lattices(X8,esk1_1(X8),k2_lattices(X8,esk2_1(X8),esk3_1(X8))) != k2_lattices(X8,k2_lattices(X8,esk1_1(X8),esk2_1(X8)),esk3_1(X8))
        | v7_lattices(X8)
        | v2_struct_0(X8)
        | ~ l1_lattices(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_lattices])])])])])])).

cnf(c_0_12,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v9_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v8_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( l3_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_18,plain,(
    ! [X15,X16,X17] :
      ( ( ~ v8_lattices(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | k1_lattices(X15,k2_lattices(X15,X16,X17),X17) = X17
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( m1_subset_1(esk4_1(X15),u1_struct_0(X15))
        | v8_lattices(X15)
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( m1_subset_1(esk5_1(X15),u1_struct_0(X15))
        | v8_lattices(X15)
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( k1_lattices(X15,k2_lattices(X15,esk4_1(X15),esk5_1(X15)),esk5_1(X15)) != esk5_1(X15)
        | v8_lattices(X15)
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( k2_lattices(X1,X2,k2_lattices(X1,X3,X4)) = k2_lattices(X1,k2_lattices(X1,X2,X3),X4)
    | v2_struct_0(X1)
    | ~ v7_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( v7_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( k2_lattices(esk6_0,X1,esk8_0) = X1
    | ~ r1_lattices(esk6_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r1_lattices(esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_26,plain,(
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

cnf(c_0_27,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk6_0,X1,esk9_0),u1_struct_0(esk6_0))
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( k2_lattices(esk6_0,k2_lattices(esk6_0,X1,X2),esk9_0) = k2_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,esk9_0))
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_22])]),c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,esk8_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_31,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k1_lattices(esk6_0,k2_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,esk9_0)),k2_lattices(esk6_0,X2,esk9_0)) = k2_lattices(esk6_0,X2,esk9_0)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k2_lattices(esk6_0,esk8_0,esk9_0)) = k2_lattices(esk6_0,esk7_0,esk9_0)
    | ~ l1_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_13]),c_0_25])])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,esk9_0)),u1_struct_0(esk6_0))
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_28]),c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( r1_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,esk9_0))
    | k1_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,esk9_0)) != k2_lattices(esk6_0,X2,esk9_0)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_28]),c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( k1_lattices(esk6_0,k2_lattices(esk6_0,esk7_0,esk9_0),k2_lattices(esk6_0,esk8_0,esk9_0)) = k2_lattices(esk6_0,esk8_0,esk9_0)
    | ~ l1_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25]),c_0_13])])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_lattices(esk6_0,k2_lattices(esk6_0,esk7_0,esk9_0),k2_lattices(esk6_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk6_0,esk7_0,esk9_0),u1_struct_0(esk6_0))
    | ~ l1_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_25]),c_0_13])])).

fof(c_0_39,plain,(
    ! [X23] :
      ( ( l1_lattices(X23)
        | ~ l3_lattices(X23) )
      & ( l2_lattices(X23)
        | ~ l3_lattices(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_40,negated_conjecture,
    ( ~ l1_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_13])]),c_0_37]),c_0_38])).

cnf(c_0_41,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( ~ l1_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_16])])).

cnf(c_0_43,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.053 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(t27_lattices, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)=>r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_lattices)).
% 0.19/0.45  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 0.19/0.45  fof(dt_k2_lattices, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_lattices)).
% 0.19/0.45  fof(d7_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v7_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>k2_lattices(X1,X2,k2_lattices(X1,X3,X4))=k2_lattices(X1,k2_lattices(X1,X2,X3),X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_lattices)).
% 0.19/0.45  fof(d8_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v8_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 0.19/0.45  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 0.19/0.45  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.19/0.45  fof(c_0_7, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)=>r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4)))))))), inference(assume_negation,[status(cth)],[t27_lattices])).
% 0.19/0.45  fof(c_0_8, plain, ![X24, X25, X26]:((~r1_lattices(X24,X25,X26)|k2_lattices(X24,X25,X26)=X25|~m1_subset_1(X26,u1_struct_0(X24))|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~v8_lattices(X24)|~v9_lattices(X24)|~l3_lattices(X24)))&(k2_lattices(X24,X25,X26)!=X25|r1_lattices(X24,X25,X26)|~m1_subset_1(X26,u1_struct_0(X24))|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~v8_lattices(X24)|~v9_lattices(X24)|~l3_lattices(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.19/0.45  fof(c_0_9, negated_conjecture, (((((~v2_struct_0(esk6_0)&v7_lattices(esk6_0))&v8_lattices(esk6_0))&v9_lattices(esk6_0))&l3_lattices(esk6_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&(m1_subset_1(esk8_0,u1_struct_0(esk6_0))&(m1_subset_1(esk9_0,u1_struct_0(esk6_0))&(r1_lattices(esk6_0,esk7_0,esk8_0)&~r1_lattices(esk6_0,k2_lattices(esk6_0,esk7_0,esk9_0),k2_lattices(esk6_0,esk8_0,esk9_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.19/0.45  fof(c_0_10, plain, ![X20, X21, X22]:(v2_struct_0(X20)|~l1_lattices(X20)|~m1_subset_1(X21,u1_struct_0(X20))|~m1_subset_1(X22,u1_struct_0(X20))|m1_subset_1(k2_lattices(X20,X21,X22),u1_struct_0(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattices])])])).
% 0.19/0.45  fof(c_0_11, plain, ![X8, X9, X10, X11]:((~v7_lattices(X8)|(~m1_subset_1(X9,u1_struct_0(X8))|(~m1_subset_1(X10,u1_struct_0(X8))|(~m1_subset_1(X11,u1_struct_0(X8))|k2_lattices(X8,X9,k2_lattices(X8,X10,X11))=k2_lattices(X8,k2_lattices(X8,X9,X10),X11))))|(v2_struct_0(X8)|~l1_lattices(X8)))&((m1_subset_1(esk1_1(X8),u1_struct_0(X8))|v7_lattices(X8)|(v2_struct_0(X8)|~l1_lattices(X8)))&((m1_subset_1(esk2_1(X8),u1_struct_0(X8))|v7_lattices(X8)|(v2_struct_0(X8)|~l1_lattices(X8)))&((m1_subset_1(esk3_1(X8),u1_struct_0(X8))|v7_lattices(X8)|(v2_struct_0(X8)|~l1_lattices(X8)))&(k2_lattices(X8,esk1_1(X8),k2_lattices(X8,esk2_1(X8),esk3_1(X8)))!=k2_lattices(X8,k2_lattices(X8,esk1_1(X8),esk2_1(X8)),esk3_1(X8))|v7_lattices(X8)|(v2_struct_0(X8)|~l1_lattices(X8))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_lattices])])])])])])).
% 0.19/0.45  cnf(c_0_12, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.45  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.45  cnf(c_0_14, negated_conjecture, (v9_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.45  cnf(c_0_15, negated_conjecture, (v8_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.45  cnf(c_0_16, negated_conjecture, (l3_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.45  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.45  fof(c_0_18, plain, ![X15, X16, X17]:((~v8_lattices(X15)|(~m1_subset_1(X16,u1_struct_0(X15))|(~m1_subset_1(X17,u1_struct_0(X15))|k1_lattices(X15,k2_lattices(X15,X16,X17),X17)=X17))|(v2_struct_0(X15)|~l3_lattices(X15)))&((m1_subset_1(esk4_1(X15),u1_struct_0(X15))|v8_lattices(X15)|(v2_struct_0(X15)|~l3_lattices(X15)))&((m1_subset_1(esk5_1(X15),u1_struct_0(X15))|v8_lattices(X15)|(v2_struct_0(X15)|~l3_lattices(X15)))&(k1_lattices(X15,k2_lattices(X15,esk4_1(X15),esk5_1(X15)),esk5_1(X15))!=esk5_1(X15)|v8_lattices(X15)|(v2_struct_0(X15)|~l3_lattices(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).
% 0.19/0.45  cnf(c_0_19, plain, (v2_struct_0(X1)|m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.45  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.45  cnf(c_0_21, plain, (k2_lattices(X1,X2,k2_lattices(X1,X3,X4))=k2_lattices(X1,k2_lattices(X1,X2,X3),X4)|v2_struct_0(X1)|~v7_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.45  cnf(c_0_22, negated_conjecture, (v7_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.45  cnf(c_0_23, negated_conjecture, (k2_lattices(esk6_0,X1,esk8_0)=X1|~r1_lattices(esk6_0,X1,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.19/0.45  cnf(c_0_24, negated_conjecture, (r1_lattices(esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.45  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.45  fof(c_0_26, plain, ![X5, X6, X7]:((~r1_lattices(X5,X6,X7)|k1_lattices(X5,X6,X7)=X7|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l2_lattices(X5)))&(k1_lattices(X5,X6,X7)!=X7|r1_lattices(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l2_lattices(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.19/0.45  cnf(c_0_27, plain, (k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3|v2_struct_0(X1)|~v8_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_28, negated_conjecture, (m1_subset_1(k2_lattices(esk6_0,X1,esk9_0),u1_struct_0(esk6_0))|~l1_lattices(esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_17])).
% 0.19/0.45  cnf(c_0_29, negated_conjecture, (k2_lattices(esk6_0,k2_lattices(esk6_0,X1,X2),esk9_0)=k2_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,esk9_0))|~l1_lattices(esk6_0)|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_20]), c_0_22])]), c_0_17])).
% 0.19/0.45  cnf(c_0_30, negated_conjecture, (k2_lattices(esk6_0,esk7_0,esk8_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.19/0.45  cnf(c_0_31, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k1_lattices(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.45  cnf(c_0_32, negated_conjecture, (k1_lattices(esk6_0,k2_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,esk9_0)),k2_lattices(esk6_0,X2,esk9_0))=k2_lattices(esk6_0,X2,esk9_0)|~l1_lattices(esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_15]), c_0_16])]), c_0_17])).
% 0.19/0.45  cnf(c_0_33, negated_conjecture, (k2_lattices(esk6_0,esk7_0,k2_lattices(esk6_0,esk8_0,esk9_0))=k2_lattices(esk6_0,esk7_0,esk9_0)|~l1_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_13]), c_0_25])])).
% 0.19/0.45  cnf(c_0_34, negated_conjecture, (m1_subset_1(k2_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,esk9_0)),u1_struct_0(esk6_0))|~l1_lattices(esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_28]), c_0_17])).
% 0.19/0.45  cnf(c_0_35, negated_conjecture, (r1_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,esk9_0))|k1_lattices(esk6_0,X1,k2_lattices(esk6_0,X2,esk9_0))!=k2_lattices(esk6_0,X2,esk9_0)|~l1_lattices(esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~m1_subset_1(X2,u1_struct_0(esk6_0))|~l2_lattices(esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_28]), c_0_17])).
% 0.19/0.45  cnf(c_0_36, negated_conjecture, (k1_lattices(esk6_0,k2_lattices(esk6_0,esk7_0,esk9_0),k2_lattices(esk6_0,esk8_0,esk9_0))=k2_lattices(esk6_0,esk8_0,esk9_0)|~l1_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_25]), c_0_13])])).
% 0.19/0.45  cnf(c_0_37, negated_conjecture, (~r1_lattices(esk6_0,k2_lattices(esk6_0,esk7_0,esk9_0),k2_lattices(esk6_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.45  cnf(c_0_38, negated_conjecture, (m1_subset_1(k2_lattices(esk6_0,esk7_0,esk9_0),u1_struct_0(esk6_0))|~l1_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_25]), c_0_13])])).
% 0.19/0.45  fof(c_0_39, plain, ![X23]:((l1_lattices(X23)|~l3_lattices(X23))&(l2_lattices(X23)|~l3_lattices(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.19/0.45  cnf(c_0_40, negated_conjecture, (~l1_lattices(esk6_0)|~l2_lattices(esk6_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_13])]), c_0_37]), c_0_38])).
% 0.19/0.45  cnf(c_0_41, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.45  cnf(c_0_42, negated_conjecture, (~l1_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_16])])).
% 0.19/0.45  cnf(c_0_43, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.45  cnf(c_0_44, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_16])]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 45
% 0.19/0.45  # Proof object clause steps            : 30
% 0.19/0.45  # Proof object formula steps           : 15
% 0.19/0.45  # Proof object conjectures             : 26
% 0.19/0.45  # Proof object clause conjectures      : 23
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 17
% 0.19/0.45  # Proof object initial formulas used   : 7
% 0.19/0.45  # Proof object generating inferences   : 13
% 0.19/0.45  # Proof object simplifying inferences  : 34
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 7
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 26
% 0.19/0.45  # Removed in clause preprocessing      : 0
% 0.19/0.45  # Initial clauses in saturation        : 26
% 0.19/0.45  # Processed clauses                    : 372
% 0.19/0.45  # ...of these trivial                  : 0
% 0.19/0.45  # ...subsumed                          : 160
% 0.19/0.45  # ...remaining for further processing  : 212
% 0.19/0.45  # Other redundant clauses eliminated   : 0
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 27
% 0.19/0.45  # Backward-rewritten                   : 0
% 0.19/0.45  # Generated clauses                    : 1089
% 0.19/0.45  # ...of the previous two non-trivial   : 1040
% 0.19/0.45  # Contextual simplify-reflections      : 15
% 0.19/0.45  # Paramodulations                      : 1089
% 0.19/0.45  # Factorizations                       : 0
% 0.19/0.45  # Equation resolutions                 : 0
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 159
% 0.19/0.45  #    Positive orientable unit clauses  : 10
% 0.19/0.45  #    Positive unorientable unit clauses: 0
% 0.19/0.45  #    Negative unit clauses             : 3
% 0.19/0.45  #    Non-unit-clauses                  : 146
% 0.19/0.45  # Current number of unprocessed clauses: 720
% 0.19/0.45  # ...number of literals in the above   : 3777
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 53
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 5322
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 2375
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 202
% 0.19/0.45  # Unit Clause-clause subsumption calls : 132
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 1
% 0.19/0.45  # BW rewrite match successes           : 0
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 41326
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.104 s
% 0.19/0.45  # System time              : 0.010 s
% 0.19/0.45  # Total time               : 0.114 s
% 0.19/0.45  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
