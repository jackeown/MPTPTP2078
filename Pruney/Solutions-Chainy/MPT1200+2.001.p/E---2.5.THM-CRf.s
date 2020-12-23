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

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 270 expanded)
%              Number of clauses        :   35 (  91 expanded)
%              Number of leaves         :    7 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  238 (1918 expanded)
%              Number of equality atoms :   28 (  50 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(dt_k2_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

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

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    & v7_lattices(esk8_0)
    & v8_lattices(esk8_0)
    & v9_lattices(esk8_0)
    & l3_lattices(esk8_0)
    & m1_subset_1(esk9_0,u1_struct_0(esk8_0))
    & m1_subset_1(esk10_0,u1_struct_0(esk8_0))
    & m1_subset_1(esk11_0,u1_struct_0(esk8_0))
    & r1_lattices(esk8_0,esk9_0,esk10_0)
    & ~ r1_lattices(esk8_0,k2_lattices(esk8_0,esk9_0,esk11_0),k2_lattices(esk8_0,esk10_0,esk11_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

cnf(c_0_10,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk10_0,u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X20,X21,X22] :
      ( ( ~ v9_lattices(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | k2_lattices(X20,X21,k1_lattices(X20,X21,X22)) = X21
        | v2_struct_0(X20)
        | ~ l3_lattices(X20) )
      & ( m1_subset_1(esk6_1(X20),u1_struct_0(X20))
        | v9_lattices(X20)
        | v2_struct_0(X20)
        | ~ l3_lattices(X20) )
      & ( m1_subset_1(esk7_1(X20),u1_struct_0(X20))
        | v9_lattices(X20)
        | v2_struct_0(X20)
        | ~ l3_lattices(X20) )
      & ( k2_lattices(X20,esk6_1(X20),k1_lattices(X20,esk6_1(X20),esk7_1(X20))) != esk6_1(X20)
        | v9_lattices(X20)
        | v2_struct_0(X20)
        | ~ l3_lattices(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).

cnf(c_0_14,negated_conjecture,
    ( k1_lattices(esk8_0,X1,esk10_0) = esk10_0
    | ~ r1_lattices(esk8_0,X1,esk10_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ l2_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( r1_lattices(esk8_0,esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,plain,(
    ! [X28] :
      ( ( l1_lattices(X28)
        | ~ l3_lattices(X28) )
      & ( l2_lattices(X28)
        | ~ l3_lattices(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_18,plain,(
    ! [X25,X26,X27] :
      ( v2_struct_0(X25)
      | ~ l1_lattices(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ m1_subset_1(X27,u1_struct_0(X25))
      | m1_subset_1(k2_lattices(X25,X26,X27),u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattices])])])).

fof(c_0_19,plain,(
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

cnf(c_0_20,plain,
    ( k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( v9_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( l3_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( k1_lattices(esk8_0,esk9_0,esk10_0) = esk10_0
    | ~ l2_lattices(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_24,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk11_0,u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_27,plain,(
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

cnf(c_0_28,plain,
    ( k2_lattices(X1,X2,k2_lattices(X1,X3,X4)) = k2_lattices(X1,k2_lattices(X1,X2,X3),X4)
    | v2_struct_0(X1)
    | ~ v7_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( v7_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( k2_lattices(esk8_0,X1,k1_lattices(esk8_0,X1,esk10_0)) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_11]),c_0_21]),c_0_22])]),c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( k1_lattices(esk8_0,esk9_0,esk10_0) = esk10_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_22])])).

cnf(c_0_32,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk8_0,X1,esk11_0),u1_struct_0(esk8_0))
    | ~ l1_lattices(esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_12])).

cnf(c_0_34,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( v8_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( k2_lattices(esk8_0,k2_lattices(esk8_0,X1,X2),esk11_0) = k2_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0))
    | ~ l1_lattices(esk8_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_26]),c_0_29])]),c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( k2_lattices(esk8_0,esk9_0,esk10_0) = esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_16])])).

cnf(c_0_38,negated_conjecture,
    ( ~ r1_lattices(esk8_0,k2_lattices(esk8_0,esk9_0,esk11_0),k2_lattices(esk8_0,esk10_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( r1_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0))
    | k1_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0)) != k2_lattices(esk8_0,X2,esk11_0)
    | ~ l1_lattices(esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ l2_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( k1_lattices(esk8_0,k2_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0)),k2_lattices(esk8_0,X2,esk11_0)) = k2_lattices(esk8_0,X2,esk11_0)
    | ~ l1_lattices(esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_35]),c_0_22])]),c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( k2_lattices(esk8_0,esk9_0,k2_lattices(esk8_0,esk10_0,esk11_0)) = k2_lattices(esk8_0,esk9_0,esk11_0)
    | ~ l1_lattices(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_11]),c_0_16])])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0)),u1_struct_0(esk8_0))
    | ~ l1_lattices(esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_33]),c_0_12])).

cnf(c_0_43,negated_conjecture,
    ( k1_lattices(esk8_0,k2_lattices(esk8_0,esk9_0,esk11_0),k2_lattices(esk8_0,esk10_0,esk11_0)) != k2_lattices(esk8_0,esk10_0,esk11_0)
    | ~ l1_lattices(esk8_0)
    | ~ m1_subset_1(k2_lattices(esk8_0,esk9_0,esk11_0),u1_struct_0(esk8_0))
    | ~ l2_lattices(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_11])])).

cnf(c_0_44,negated_conjecture,
    ( k1_lattices(esk8_0,k2_lattices(esk8_0,esk9_0,esk11_0),k2_lattices(esk8_0,esk10_0,esk11_0)) = k2_lattices(esk8_0,esk10_0,esk11_0)
    | ~ l1_lattices(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_16]),c_0_11])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk8_0,esk9_0,esk11_0),u1_struct_0(esk8_0))
    | ~ l1_lattices(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_41]),c_0_16]),c_0_11])])).

cnf(c_0_46,negated_conjecture,
    ( ~ l1_lattices(esk8_0)
    | ~ l2_lattices(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_47,negated_conjecture,
    ( ~ l1_lattices(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_24]),c_0_22])])).

cnf(c_0_48,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:03:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.34  # Version: 2.5pre002
% 0.21/0.34  # No SInE strategy applied
% 0.21/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.42  #
% 0.21/0.42  # Preprocessing time       : 0.028 s
% 0.21/0.42  # Presaturation interreduction done
% 0.21/0.42  
% 0.21/0.42  # Proof found!
% 0.21/0.42  # SZS status Theorem
% 0.21/0.42  # SZS output start CNFRefutation
% 0.21/0.42  fof(t27_lattices, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)=>r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_lattices)).
% 0.21/0.42  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 0.21/0.42  fof(d9_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v9_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattices)).
% 0.21/0.42  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.21/0.42  fof(dt_k2_lattices, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_lattices)).
% 0.21/0.42  fof(d7_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v7_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>k2_lattices(X1,X2,k2_lattices(X1,X3,X4))=k2_lattices(X1,k2_lattices(X1,X2,X3),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_lattices)).
% 0.21/0.42  fof(d8_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v8_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattices)).
% 0.21/0.42  fof(c_0_7, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)=>r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4)))))))), inference(assume_negation,[status(cth)],[t27_lattices])).
% 0.21/0.42  fof(c_0_8, plain, ![X5, X6, X7]:((~r1_lattices(X5,X6,X7)|k1_lattices(X5,X6,X7)=X7|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l2_lattices(X5)))&(k1_lattices(X5,X6,X7)!=X7|r1_lattices(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l2_lattices(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.21/0.42  fof(c_0_9, negated_conjecture, (((((~v2_struct_0(esk8_0)&v7_lattices(esk8_0))&v8_lattices(esk8_0))&v9_lattices(esk8_0))&l3_lattices(esk8_0))&(m1_subset_1(esk9_0,u1_struct_0(esk8_0))&(m1_subset_1(esk10_0,u1_struct_0(esk8_0))&(m1_subset_1(esk11_0,u1_struct_0(esk8_0))&(r1_lattices(esk8_0,esk9_0,esk10_0)&~r1_lattices(esk8_0,k2_lattices(esk8_0,esk9_0,esk11_0),k2_lattices(esk8_0,esk10_0,esk11_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.21/0.42  cnf(c_0_10, plain, (k1_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.42  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk10_0,u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.42  cnf(c_0_12, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.42  fof(c_0_13, plain, ![X20, X21, X22]:((~v9_lattices(X20)|(~m1_subset_1(X21,u1_struct_0(X20))|(~m1_subset_1(X22,u1_struct_0(X20))|k2_lattices(X20,X21,k1_lattices(X20,X21,X22))=X21))|(v2_struct_0(X20)|~l3_lattices(X20)))&((m1_subset_1(esk6_1(X20),u1_struct_0(X20))|v9_lattices(X20)|(v2_struct_0(X20)|~l3_lattices(X20)))&((m1_subset_1(esk7_1(X20),u1_struct_0(X20))|v9_lattices(X20)|(v2_struct_0(X20)|~l3_lattices(X20)))&(k2_lattices(X20,esk6_1(X20),k1_lattices(X20,esk6_1(X20),esk7_1(X20)))!=esk6_1(X20)|v9_lattices(X20)|(v2_struct_0(X20)|~l3_lattices(X20)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).
% 0.21/0.42  cnf(c_0_14, negated_conjecture, (k1_lattices(esk8_0,X1,esk10_0)=esk10_0|~r1_lattices(esk8_0,X1,esk10_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))|~l2_lattices(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])).
% 0.21/0.42  cnf(c_0_15, negated_conjecture, (r1_lattices(esk8_0,esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.42  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.42  fof(c_0_17, plain, ![X28]:((l1_lattices(X28)|~l3_lattices(X28))&(l2_lattices(X28)|~l3_lattices(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.21/0.42  fof(c_0_18, plain, ![X25, X26, X27]:(v2_struct_0(X25)|~l1_lattices(X25)|~m1_subset_1(X26,u1_struct_0(X25))|~m1_subset_1(X27,u1_struct_0(X25))|m1_subset_1(k2_lattices(X25,X26,X27),u1_struct_0(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattices])])])).
% 0.21/0.42  fof(c_0_19, plain, ![X8, X9, X10, X11]:((~v7_lattices(X8)|(~m1_subset_1(X9,u1_struct_0(X8))|(~m1_subset_1(X10,u1_struct_0(X8))|(~m1_subset_1(X11,u1_struct_0(X8))|k2_lattices(X8,X9,k2_lattices(X8,X10,X11))=k2_lattices(X8,k2_lattices(X8,X9,X10),X11))))|(v2_struct_0(X8)|~l1_lattices(X8)))&((m1_subset_1(esk1_1(X8),u1_struct_0(X8))|v7_lattices(X8)|(v2_struct_0(X8)|~l1_lattices(X8)))&((m1_subset_1(esk2_1(X8),u1_struct_0(X8))|v7_lattices(X8)|(v2_struct_0(X8)|~l1_lattices(X8)))&((m1_subset_1(esk3_1(X8),u1_struct_0(X8))|v7_lattices(X8)|(v2_struct_0(X8)|~l1_lattices(X8)))&(k2_lattices(X8,esk1_1(X8),k2_lattices(X8,esk2_1(X8),esk3_1(X8)))!=k2_lattices(X8,k2_lattices(X8,esk1_1(X8),esk2_1(X8)),esk3_1(X8))|v7_lattices(X8)|(v2_struct_0(X8)|~l1_lattices(X8))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_lattices])])])])])])).
% 0.21/0.42  cnf(c_0_20, plain, (k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2|v2_struct_0(X1)|~v9_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.42  cnf(c_0_21, negated_conjecture, (v9_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.42  cnf(c_0_22, negated_conjecture, (l3_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.42  cnf(c_0_23, negated_conjecture, (k1_lattices(esk8_0,esk9_0,esk10_0)=esk10_0|~l2_lattices(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.21/0.42  cnf(c_0_24, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.42  cnf(c_0_25, plain, (v2_struct_0(X1)|m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.42  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk11_0,u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.42  fof(c_0_27, plain, ![X15, X16, X17]:((~v8_lattices(X15)|(~m1_subset_1(X16,u1_struct_0(X15))|(~m1_subset_1(X17,u1_struct_0(X15))|k1_lattices(X15,k2_lattices(X15,X16,X17),X17)=X17))|(v2_struct_0(X15)|~l3_lattices(X15)))&((m1_subset_1(esk4_1(X15),u1_struct_0(X15))|v8_lattices(X15)|(v2_struct_0(X15)|~l3_lattices(X15)))&((m1_subset_1(esk5_1(X15),u1_struct_0(X15))|v8_lattices(X15)|(v2_struct_0(X15)|~l3_lattices(X15)))&(k1_lattices(X15,k2_lattices(X15,esk4_1(X15),esk5_1(X15)),esk5_1(X15))!=esk5_1(X15)|v8_lattices(X15)|(v2_struct_0(X15)|~l3_lattices(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).
% 0.21/0.42  cnf(c_0_28, plain, (k2_lattices(X1,X2,k2_lattices(X1,X3,X4))=k2_lattices(X1,k2_lattices(X1,X2,X3),X4)|v2_struct_0(X1)|~v7_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.42  cnf(c_0_29, negated_conjecture, (v7_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.42  cnf(c_0_30, negated_conjecture, (k2_lattices(esk8_0,X1,k1_lattices(esk8_0,X1,esk10_0))=X1|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_11]), c_0_21]), c_0_22])]), c_0_12])).
% 0.21/0.42  cnf(c_0_31, negated_conjecture, (k1_lattices(esk8_0,esk9_0,esk10_0)=esk10_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_22])])).
% 0.21/0.42  cnf(c_0_32, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k1_lattices(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.42  cnf(c_0_33, negated_conjecture, (m1_subset_1(k2_lattices(esk8_0,X1,esk11_0),u1_struct_0(esk8_0))|~l1_lattices(esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_12])).
% 0.21/0.42  cnf(c_0_34, plain, (k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3|v2_struct_0(X1)|~v8_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.42  cnf(c_0_35, negated_conjecture, (v8_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.42  cnf(c_0_36, negated_conjecture, (k2_lattices(esk8_0,k2_lattices(esk8_0,X1,X2),esk11_0)=k2_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0))|~l1_lattices(esk8_0)|~m1_subset_1(X2,u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_26]), c_0_29])]), c_0_12])).
% 0.21/0.42  cnf(c_0_37, negated_conjecture, (k2_lattices(esk8_0,esk9_0,esk10_0)=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_16])])).
% 0.21/0.42  cnf(c_0_38, negated_conjecture, (~r1_lattices(esk8_0,k2_lattices(esk8_0,esk9_0,esk11_0),k2_lattices(esk8_0,esk10_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.42  cnf(c_0_39, negated_conjecture, (r1_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0))|k1_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0))!=k2_lattices(esk8_0,X2,esk11_0)|~l1_lattices(esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))|~m1_subset_1(X2,u1_struct_0(esk8_0))|~l2_lattices(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_12])).
% 0.21/0.42  cnf(c_0_40, negated_conjecture, (k1_lattices(esk8_0,k2_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0)),k2_lattices(esk8_0,X2,esk11_0))=k2_lattices(esk8_0,X2,esk11_0)|~l1_lattices(esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))|~m1_subset_1(X2,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_35]), c_0_22])]), c_0_12])).
% 0.21/0.42  cnf(c_0_41, negated_conjecture, (k2_lattices(esk8_0,esk9_0,k2_lattices(esk8_0,esk10_0,esk11_0))=k2_lattices(esk8_0,esk9_0,esk11_0)|~l1_lattices(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_11]), c_0_16])])).
% 0.21/0.42  cnf(c_0_42, negated_conjecture, (m1_subset_1(k2_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0)),u1_struct_0(esk8_0))|~l1_lattices(esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))|~m1_subset_1(X2,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_33]), c_0_12])).
% 0.21/0.42  cnf(c_0_43, negated_conjecture, (k1_lattices(esk8_0,k2_lattices(esk8_0,esk9_0,esk11_0),k2_lattices(esk8_0,esk10_0,esk11_0))!=k2_lattices(esk8_0,esk10_0,esk11_0)|~l1_lattices(esk8_0)|~m1_subset_1(k2_lattices(esk8_0,esk9_0,esk11_0),u1_struct_0(esk8_0))|~l2_lattices(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_11])])).
% 0.21/0.42  cnf(c_0_44, negated_conjecture, (k1_lattices(esk8_0,k2_lattices(esk8_0,esk9_0,esk11_0),k2_lattices(esk8_0,esk10_0,esk11_0))=k2_lattices(esk8_0,esk10_0,esk11_0)|~l1_lattices(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_16]), c_0_11])])).
% 0.21/0.42  cnf(c_0_45, negated_conjecture, (m1_subset_1(k2_lattices(esk8_0,esk9_0,esk11_0),u1_struct_0(esk8_0))|~l1_lattices(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_41]), c_0_16]), c_0_11])])).
% 0.21/0.42  cnf(c_0_46, negated_conjecture, (~l1_lattices(esk8_0)|~l2_lattices(esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.21/0.42  cnf(c_0_47, negated_conjecture, (~l1_lattices(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_24]), c_0_22])])).
% 0.21/0.42  cnf(c_0_48, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.42  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_22])]), ['proof']).
% 0.21/0.42  # SZS output end CNFRefutation
% 0.21/0.42  # Proof object total steps             : 50
% 0.21/0.42  # Proof object clause steps            : 35
% 0.21/0.42  # Proof object formula steps           : 15
% 0.21/0.42  # Proof object conjectures             : 30
% 0.21/0.42  # Proof object clause conjectures      : 27
% 0.21/0.42  # Proof object formula conjectures     : 3
% 0.21/0.42  # Proof object initial clauses used    : 18
% 0.21/0.42  # Proof object initial formulas used   : 7
% 0.21/0.42  # Proof object generating inferences   : 17
% 0.21/0.42  # Proof object simplifying inferences  : 37
% 0.21/0.42  # Training examples: 0 positive, 0 negative
% 0.21/0.42  # Parsed axioms                        : 7
% 0.21/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.42  # Initial clauses                      : 28
% 0.21/0.42  # Removed in clause preprocessing      : 0
% 0.21/0.42  # Initial clauses in saturation        : 28
% 0.21/0.42  # Processed clauses                    : 394
% 0.21/0.42  # ...of these trivial                  : 0
% 0.21/0.42  # ...subsumed                          : 185
% 0.21/0.42  # ...remaining for further processing  : 209
% 0.21/0.42  # Other redundant clauses eliminated   : 0
% 0.21/0.42  # Clauses deleted for lack of memory   : 0
% 0.21/0.42  # Backward-subsumed                    : 23
% 0.21/0.42  # Backward-rewritten                   : 1
% 0.21/0.42  # Generated clauses                    : 1268
% 0.21/0.42  # ...of the previous two non-trivial   : 1225
% 0.21/0.42  # Contextual simplify-reflections      : 12
% 0.21/0.42  # Paramodulations                      : 1268
% 0.21/0.42  # Factorizations                       : 0
% 0.21/0.42  # Equation resolutions                 : 0
% 0.21/0.42  # Propositional unsat checks           : 0
% 0.21/0.42  #    Propositional check models        : 0
% 0.21/0.42  #    Propositional check unsatisfiable : 0
% 0.21/0.42  #    Propositional clauses             : 0
% 0.21/0.42  #    Propositional clauses after purity: 0
% 0.21/0.42  #    Propositional unsat core size     : 0
% 0.21/0.42  #    Propositional preprocessing time  : 0.000
% 0.21/0.42  #    Propositional encoding time       : 0.000
% 0.21/0.42  #    Propositional solver time         : 0.000
% 0.21/0.42  #    Success case prop preproc time    : 0.000
% 0.21/0.42  #    Success case prop encoding time   : 0.000
% 0.21/0.42  #    Success case prop solver time     : 0.000
% 0.21/0.42  # Current number of processed clauses  : 157
% 0.21/0.42  #    Positive orientable unit clauses  : 10
% 0.21/0.42  #    Positive unorientable unit clauses: 0
% 0.21/0.42  #    Negative unit clauses             : 3
% 0.21/0.42  #    Non-unit-clauses                  : 144
% 0.21/0.42  # Current number of unprocessed clauses: 887
% 0.21/0.42  # ...number of literals in the above   : 4902
% 0.21/0.42  # Current number of archived formulas  : 0
% 0.21/0.42  # Current number of archived clauses   : 52
% 0.21/0.42  # Clause-clause subsumption calls (NU) : 8652
% 0.21/0.42  # Rec. Clause-clause subsumption calls : 3967
% 0.21/0.42  # Non-unit clause-clause subsumptions  : 220
% 0.21/0.42  # Unit Clause-clause subsumption calls : 131
% 0.21/0.42  # Rewrite failures with RHS unbound    : 0
% 0.21/0.42  # BW rewrite match attempts            : 2
% 0.21/0.42  # BW rewrite match successes           : 1
% 0.21/0.42  # Condensation attempts                : 0
% 0.21/0.42  # Condensation successes               : 0
% 0.21/0.42  # Termbank termtop insertions          : 48075
% 0.21/0.42  
% 0.21/0.42  # -------------------------------------------------
% 0.21/0.42  # User time                : 0.075 s
% 0.21/0.42  # System time              : 0.006 s
% 0.21/0.42  # Total time               : 0.081 s
% 0.21/0.42  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
