%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:23 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 352 expanded)
%              Number of clauses        :   32 ( 114 expanded)
%              Number of leaves         :    7 (  85 expanded)
%              Depth                    :   10
%              Number of atoms          :  242 (2600 expanded)
%              Number of equality atoms :   27 (  54 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

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
    ! [X26,X27,X28] :
      ( ( ~ r1_lattices(X26,X27,X28)
        | k2_lattices(X26,X27,X28) = X27
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v8_lattices(X26)
        | ~ v9_lattices(X26)
        | ~ l3_lattices(X26) )
      & ( k2_lattices(X26,X27,X28) != X27
        | r1_lattices(X26,X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v8_lattices(X26)
        | ~ v9_lattices(X26)
        | ~ l3_lattices(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

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

fof(c_0_10,plain,(
    ! [X22,X23,X24] :
      ( v2_struct_0(X22)
      | ~ l1_lattices(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | ~ m1_subset_1(X24,u1_struct_0(X22))
      | m1_subset_1(k2_lattices(X22,X23,X24),u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattices])])])).

fof(c_0_11,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ v7_lattices(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X8,u1_struct_0(X5))
        | k2_lattices(X5,X6,k2_lattices(X5,X7,X8)) = k2_lattices(X5,k2_lattices(X5,X6,X7),X8)
        | v2_struct_0(X5)
        | ~ l1_lattices(X5) )
      & ( m1_subset_1(esk1_1(X5),u1_struct_0(X5))
        | v7_lattices(X5)
        | v2_struct_0(X5)
        | ~ l1_lattices(X5) )
      & ( m1_subset_1(esk2_1(X5),u1_struct_0(X5))
        | v7_lattices(X5)
        | v2_struct_0(X5)
        | ~ l1_lattices(X5) )
      & ( m1_subset_1(esk3_1(X5),u1_struct_0(X5))
        | v7_lattices(X5)
        | v2_struct_0(X5)
        | ~ l1_lattices(X5) )
      & ( k2_lattices(X5,esk1_1(X5),k2_lattices(X5,esk2_1(X5),esk3_1(X5))) != k2_lattices(X5,k2_lattices(X5,esk1_1(X5),esk2_1(X5)),esk3_1(X5))
        | v7_lattices(X5)
        | v2_struct_0(X5)
        | ~ l1_lattices(X5) ) ) ),
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
    ( m1_subset_1(esk10_0,u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v9_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v8_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( l3_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_18,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v8_lattices(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | k1_lattices(X12,k2_lattices(X12,X13,X14),X14) = X14
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk4_1(X12),u1_struct_0(X12))
        | v8_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk5_1(X12),u1_struct_0(X12))
        | v8_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( k1_lattices(X12,k2_lattices(X12,esk4_1(X12),esk5_1(X12)),esk5_1(X12)) != esk5_1(X12)
        | v8_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk11_0,u1_struct_0(esk8_0)) ),
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
    ( v7_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( k2_lattices(esk8_0,X1,esk10_0) = X1
    | ~ r1_lattices(esk8_0,X1,esk10_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r1_lattices(esk8_0,esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_26,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v9_lattices(X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | k2_lattices(X17,X18,k1_lattices(X17,X18,X19)) = X18
        | v2_struct_0(X17)
        | ~ l3_lattices(X17) )
      & ( m1_subset_1(esk6_1(X17),u1_struct_0(X17))
        | v9_lattices(X17)
        | v2_struct_0(X17)
        | ~ l3_lattices(X17) )
      & ( m1_subset_1(esk7_1(X17),u1_struct_0(X17))
        | v9_lattices(X17)
        | v2_struct_0(X17)
        | ~ l3_lattices(X17) )
      & ( k2_lattices(X17,esk6_1(X17),k1_lattices(X17,esk6_1(X17),esk7_1(X17))) != esk6_1(X17)
        | v9_lattices(X17)
        | v2_struct_0(X17)
        | ~ l3_lattices(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).

cnf(c_0_27,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk8_0,X1,esk11_0),u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ l1_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( k2_lattices(esk8_0,k2_lattices(esk8_0,X1,X2),esk11_0) = k2_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ l1_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_22])]),c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( k2_lattices(esk8_0,esk9_0,esk10_0) = esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_31,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X3) != X2
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,plain,
    ( k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k1_lattices(esk8_0,k2_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0)),k2_lattices(esk8_0,X2,esk11_0)) = k2_lattices(esk8_0,X2,esk11_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ l1_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( k2_lattices(esk8_0,esk9_0,k2_lattices(esk8_0,esk10_0,esk11_0)) = k2_lattices(esk8_0,esk9_0,esk11_0)
    | ~ l1_lattices(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_13]),c_0_25])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0)),u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ l1_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_28]),c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_lattices(esk8_0,k2_lattices(esk8_0,esk9_0,esk11_0),k2_lattices(esk8_0,esk10_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,negated_conjecture,
    ( r1_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0))
    | k2_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0)) != X1
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ l1_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_28]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( k2_lattices(esk8_0,X1,k1_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0))) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ l1_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_28]),c_0_14]),c_0_16])]),c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( k1_lattices(esk8_0,k2_lattices(esk8_0,esk9_0,esk11_0),k2_lattices(esk8_0,esk10_0,esk11_0)) = k2_lattices(esk8_0,esk10_0,esk11_0)
    | ~ l1_lattices(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_25]),c_0_13])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk8_0,esk9_0,esk11_0),u1_struct_0(esk8_0))
    | ~ l1_lattices(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_34]),c_0_25]),c_0_13])])).

cnf(c_0_41,negated_conjecture,
    ( k2_lattices(esk8_0,k2_lattices(esk8_0,esk9_0,esk11_0),k2_lattices(esk8_0,esk10_0,esk11_0)) != k2_lattices(esk8_0,esk9_0,esk11_0)
    | ~ m1_subset_1(k2_lattices(esk8_0,esk9_0,esk11_0),u1_struct_0(esk8_0))
    | ~ l1_lattices(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_13])])).

cnf(c_0_42,negated_conjecture,
    ( k2_lattices(esk8_0,k2_lattices(esk8_0,esk9_0,esk11_0),k2_lattices(esk8_0,esk10_0,esk11_0)) = k2_lattices(esk8_0,esk9_0,esk11_0)
    | ~ l1_lattices(esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_13])]),c_0_40])).

fof(c_0_43,plain,(
    ! [X25] :
      ( ( l1_lattices(X25)
        | ~ l3_lattices(X25) )
      & ( l2_lattices(X25)
        | ~ l3_lattices(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_44,negated_conjecture,
    ( ~ l1_lattices(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_40])).

cnf(c_0_45,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.41  #
% 0.13/0.41  # Preprocessing time       : 0.029 s
% 0.13/0.41  # Presaturation interreduction done
% 0.13/0.41  
% 0.13/0.41  # Proof found!
% 0.13/0.41  # SZS status Theorem
% 0.13/0.41  # SZS output start CNFRefutation
% 0.13/0.41  fof(t27_lattices, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)=>r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_lattices)).
% 0.13/0.41  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 0.13/0.41  fof(dt_k2_lattices, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_lattices)).
% 0.13/0.41  fof(d7_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v7_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>k2_lattices(X1,X2,k2_lattices(X1,X3,X4))=k2_lattices(X1,k2_lattices(X1,X2,X3),X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_lattices)).
% 0.13/0.41  fof(d8_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v8_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 0.13/0.41  fof(d9_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v9_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattices)).
% 0.13/0.41  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.13/0.41  fof(c_0_7, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)=>r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4)))))))), inference(assume_negation,[status(cth)],[t27_lattices])).
% 0.13/0.41  fof(c_0_8, plain, ![X26, X27, X28]:((~r1_lattices(X26,X27,X28)|k2_lattices(X26,X27,X28)=X27|~m1_subset_1(X28,u1_struct_0(X26))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v8_lattices(X26)|~v9_lattices(X26)|~l3_lattices(X26)))&(k2_lattices(X26,X27,X28)!=X27|r1_lattices(X26,X27,X28)|~m1_subset_1(X28,u1_struct_0(X26))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v8_lattices(X26)|~v9_lattices(X26)|~l3_lattices(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.13/0.41  fof(c_0_9, negated_conjecture, (((((~v2_struct_0(esk8_0)&v7_lattices(esk8_0))&v8_lattices(esk8_0))&v9_lattices(esk8_0))&l3_lattices(esk8_0))&(m1_subset_1(esk9_0,u1_struct_0(esk8_0))&(m1_subset_1(esk10_0,u1_struct_0(esk8_0))&(m1_subset_1(esk11_0,u1_struct_0(esk8_0))&(r1_lattices(esk8_0,esk9_0,esk10_0)&~r1_lattices(esk8_0,k2_lattices(esk8_0,esk9_0,esk11_0),k2_lattices(esk8_0,esk10_0,esk11_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.13/0.41  fof(c_0_10, plain, ![X22, X23, X24]:(v2_struct_0(X22)|~l1_lattices(X22)|~m1_subset_1(X23,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|m1_subset_1(k2_lattices(X22,X23,X24),u1_struct_0(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattices])])])).
% 0.13/0.41  fof(c_0_11, plain, ![X5, X6, X7, X8]:((~v7_lattices(X5)|(~m1_subset_1(X6,u1_struct_0(X5))|(~m1_subset_1(X7,u1_struct_0(X5))|(~m1_subset_1(X8,u1_struct_0(X5))|k2_lattices(X5,X6,k2_lattices(X5,X7,X8))=k2_lattices(X5,k2_lattices(X5,X6,X7),X8))))|(v2_struct_0(X5)|~l1_lattices(X5)))&((m1_subset_1(esk1_1(X5),u1_struct_0(X5))|v7_lattices(X5)|(v2_struct_0(X5)|~l1_lattices(X5)))&((m1_subset_1(esk2_1(X5),u1_struct_0(X5))|v7_lattices(X5)|(v2_struct_0(X5)|~l1_lattices(X5)))&((m1_subset_1(esk3_1(X5),u1_struct_0(X5))|v7_lattices(X5)|(v2_struct_0(X5)|~l1_lattices(X5)))&(k2_lattices(X5,esk1_1(X5),k2_lattices(X5,esk2_1(X5),esk3_1(X5)))!=k2_lattices(X5,k2_lattices(X5,esk1_1(X5),esk2_1(X5)),esk3_1(X5))|v7_lattices(X5)|(v2_struct_0(X5)|~l1_lattices(X5))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_lattices])])])])])])).
% 0.13/0.41  cnf(c_0_12, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.41  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk10_0,u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_14, negated_conjecture, (v9_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_15, negated_conjecture, (v8_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_16, negated_conjecture, (l3_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  fof(c_0_18, plain, ![X12, X13, X14]:((~v8_lattices(X12)|(~m1_subset_1(X13,u1_struct_0(X12))|(~m1_subset_1(X14,u1_struct_0(X12))|k1_lattices(X12,k2_lattices(X12,X13,X14),X14)=X14))|(v2_struct_0(X12)|~l3_lattices(X12)))&((m1_subset_1(esk4_1(X12),u1_struct_0(X12))|v8_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))&((m1_subset_1(esk5_1(X12),u1_struct_0(X12))|v8_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))&(k1_lattices(X12,k2_lattices(X12,esk4_1(X12),esk5_1(X12)),esk5_1(X12))!=esk5_1(X12)|v8_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).
% 0.13/0.41  cnf(c_0_19, plain, (v2_struct_0(X1)|m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.41  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk11_0,u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_21, plain, (k2_lattices(X1,X2,k2_lattices(X1,X3,X4))=k2_lattices(X1,k2_lattices(X1,X2,X3),X4)|v2_struct_0(X1)|~v7_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.41  cnf(c_0_22, negated_conjecture, (v7_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_23, negated_conjecture, (k2_lattices(esk8_0,X1,esk10_0)=X1|~r1_lattices(esk8_0,X1,esk10_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.13/0.41  cnf(c_0_24, negated_conjecture, (r1_lattices(esk8_0,esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  fof(c_0_26, plain, ![X17, X18, X19]:((~v9_lattices(X17)|(~m1_subset_1(X18,u1_struct_0(X17))|(~m1_subset_1(X19,u1_struct_0(X17))|k2_lattices(X17,X18,k1_lattices(X17,X18,X19))=X18))|(v2_struct_0(X17)|~l3_lattices(X17)))&((m1_subset_1(esk6_1(X17),u1_struct_0(X17))|v9_lattices(X17)|(v2_struct_0(X17)|~l3_lattices(X17)))&((m1_subset_1(esk7_1(X17),u1_struct_0(X17))|v9_lattices(X17)|(v2_struct_0(X17)|~l3_lattices(X17)))&(k2_lattices(X17,esk6_1(X17),k1_lattices(X17,esk6_1(X17),esk7_1(X17)))!=esk6_1(X17)|v9_lattices(X17)|(v2_struct_0(X17)|~l3_lattices(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).
% 0.13/0.41  cnf(c_0_27, plain, (k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3|v2_struct_0(X1)|~v8_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.41  cnf(c_0_28, negated_conjecture, (m1_subset_1(k2_lattices(esk8_0,X1,esk11_0),u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))|~l1_lattices(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_17])).
% 0.13/0.41  cnf(c_0_29, negated_conjecture, (k2_lattices(esk8_0,k2_lattices(esk8_0,X1,X2),esk11_0)=k2_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0))|~m1_subset_1(X2,u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))|~l1_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_20]), c_0_22])]), c_0_17])).
% 0.13/0.41  cnf(c_0_30, negated_conjecture, (k2_lattices(esk8_0,esk9_0,esk10_0)=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.13/0.41  cnf(c_0_31, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k2_lattices(X1,X2,X3)!=X2|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.41  cnf(c_0_32, plain, (k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2|v2_struct_0(X1)|~v9_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.41  cnf(c_0_33, negated_conjecture, (k1_lattices(esk8_0,k2_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0)),k2_lattices(esk8_0,X2,esk11_0))=k2_lattices(esk8_0,X2,esk11_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))|~m1_subset_1(X2,u1_struct_0(esk8_0))|~l1_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_15]), c_0_16])]), c_0_17])).
% 0.13/0.41  cnf(c_0_34, negated_conjecture, (k2_lattices(esk8_0,esk9_0,k2_lattices(esk8_0,esk10_0,esk11_0))=k2_lattices(esk8_0,esk9_0,esk11_0)|~l1_lattices(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_13]), c_0_25])])).
% 0.13/0.41  cnf(c_0_35, negated_conjecture, (m1_subset_1(k2_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0)),u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))|~m1_subset_1(X2,u1_struct_0(esk8_0))|~l1_lattices(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_28]), c_0_17])).
% 0.13/0.41  cnf(c_0_36, negated_conjecture, (~r1_lattices(esk8_0,k2_lattices(esk8_0,esk9_0,esk11_0),k2_lattices(esk8_0,esk10_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_37, negated_conjecture, (r1_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0))|k2_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0))!=X1|~m1_subset_1(X1,u1_struct_0(esk8_0))|~m1_subset_1(X2,u1_struct_0(esk8_0))|~l1_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_28]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.13/0.41  cnf(c_0_38, negated_conjecture, (k2_lattices(esk8_0,X1,k1_lattices(esk8_0,X1,k2_lattices(esk8_0,X2,esk11_0)))=X1|~m1_subset_1(X1,u1_struct_0(esk8_0))|~m1_subset_1(X2,u1_struct_0(esk8_0))|~l1_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_28]), c_0_14]), c_0_16])]), c_0_17])).
% 0.13/0.41  cnf(c_0_39, negated_conjecture, (k1_lattices(esk8_0,k2_lattices(esk8_0,esk9_0,esk11_0),k2_lattices(esk8_0,esk10_0,esk11_0))=k2_lattices(esk8_0,esk10_0,esk11_0)|~l1_lattices(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_25]), c_0_13])])).
% 0.13/0.41  cnf(c_0_40, negated_conjecture, (m1_subset_1(k2_lattices(esk8_0,esk9_0,esk11_0),u1_struct_0(esk8_0))|~l1_lattices(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_34]), c_0_25]), c_0_13])])).
% 0.13/0.41  cnf(c_0_41, negated_conjecture, (k2_lattices(esk8_0,k2_lattices(esk8_0,esk9_0,esk11_0),k2_lattices(esk8_0,esk10_0,esk11_0))!=k2_lattices(esk8_0,esk9_0,esk11_0)|~m1_subset_1(k2_lattices(esk8_0,esk9_0,esk11_0),u1_struct_0(esk8_0))|~l1_lattices(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_13])])).
% 0.13/0.41  cnf(c_0_42, negated_conjecture, (k2_lattices(esk8_0,k2_lattices(esk8_0,esk9_0,esk11_0),k2_lattices(esk8_0,esk10_0,esk11_0))=k2_lattices(esk8_0,esk9_0,esk11_0)|~l1_lattices(esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_13])]), c_0_40])).
% 0.13/0.41  fof(c_0_43, plain, ![X25]:((l1_lattices(X25)|~l3_lattices(X25))&(l2_lattices(X25)|~l3_lattices(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.13/0.41  cnf(c_0_44, negated_conjecture, (~l1_lattices(esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_40])).
% 0.13/0.41  cnf(c_0_45, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.41  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_16])]), ['proof']).
% 0.13/0.41  # SZS output end CNFRefutation
% 0.13/0.41  # Proof object total steps             : 47
% 0.13/0.41  # Proof object clause steps            : 32
% 0.13/0.41  # Proof object formula steps           : 15
% 0.13/0.41  # Proof object conjectures             : 28
% 0.13/0.41  # Proof object clause conjectures      : 25
% 0.13/0.41  # Proof object formula conjectures     : 3
% 0.13/0.41  # Proof object initial clauses used    : 17
% 0.13/0.41  # Proof object initial formulas used   : 7
% 0.13/0.41  # Proof object generating inferences   : 15
% 0.13/0.41  # Proof object simplifying inferences  : 42
% 0.13/0.41  # Training examples: 0 positive, 0 negative
% 0.13/0.41  # Parsed axioms                        : 7
% 0.13/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.41  # Initial clauses                      : 28
% 0.13/0.41  # Removed in clause preprocessing      : 0
% 0.13/0.41  # Initial clauses in saturation        : 28
% 0.13/0.41  # Processed clauses                    : 267
% 0.13/0.41  # ...of these trivial                  : 0
% 0.13/0.41  # ...subsumed                          : 97
% 0.13/0.41  # ...remaining for further processing  : 170
% 0.13/0.41  # Other redundant clauses eliminated   : 0
% 0.13/0.41  # Clauses deleted for lack of memory   : 0
% 0.13/0.41  # Backward-subsumed                    : 0
% 0.13/0.41  # Backward-rewritten                   : 0
% 0.13/0.41  # Generated clauses                    : 732
% 0.13/0.41  # ...of the previous two non-trivial   : 694
% 0.13/0.41  # Contextual simplify-reflections      : 6
% 0.13/0.41  # Paramodulations                      : 732
% 0.13/0.41  # Factorizations                       : 0
% 0.13/0.41  # Equation resolutions                 : 0
% 0.13/0.41  # Propositional unsat checks           : 0
% 0.13/0.41  #    Propositional check models        : 0
% 0.13/0.41  #    Propositional check unsatisfiable : 0
% 0.13/0.41  #    Propositional clauses             : 0
% 0.13/0.41  #    Propositional clauses after purity: 0
% 0.13/0.41  #    Propositional unsat core size     : 0
% 0.13/0.41  #    Propositional preprocessing time  : 0.000
% 0.13/0.41  #    Propositional encoding time       : 0.000
% 0.13/0.41  #    Propositional solver time         : 0.000
% 0.13/0.41  #    Success case prop preproc time    : 0.000
% 0.13/0.41  #    Success case prop encoding time   : 0.000
% 0.13/0.41  #    Success case prop solver time     : 0.000
% 0.13/0.41  # Current number of processed clauses  : 142
% 0.13/0.41  #    Positive orientable unit clauses  : 10
% 0.13/0.41  #    Positive unorientable unit clauses: 0
% 0.13/0.41  #    Negative unit clauses             : 3
% 0.13/0.41  #    Non-unit-clauses                  : 129
% 0.13/0.41  # Current number of unprocessed clauses: 483
% 0.13/0.41  # ...number of literals in the above   : 2369
% 0.13/0.41  # Current number of archived formulas  : 0
% 0.13/0.41  # Current number of archived clauses   : 28
% 0.13/0.41  # Clause-clause subsumption calls (NU) : 4361
% 0.13/0.41  # Rec. Clause-clause subsumption calls : 2474
% 0.13/0.41  # Non-unit clause-clause subsumptions  : 103
% 0.13/0.41  # Unit Clause-clause subsumption calls : 101
% 0.13/0.41  # Rewrite failures with RHS unbound    : 0
% 0.13/0.41  # BW rewrite match attempts            : 1
% 0.13/0.41  # BW rewrite match successes           : 0
% 0.13/0.41  # Condensation attempts                : 0
% 0.13/0.41  # Condensation successes               : 0
% 0.13/0.41  # Termbank termtop insertions          : 27163
% 0.13/0.41  
% 0.13/0.41  # -------------------------------------------------
% 0.13/0.41  # User time                : 0.055 s
% 0.13/0.41  # System time              : 0.006 s
% 0.13/0.41  # Total time               : 0.062 s
% 0.13/0.41  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
