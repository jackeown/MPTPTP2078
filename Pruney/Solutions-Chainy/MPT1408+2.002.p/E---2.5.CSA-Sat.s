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
% DateTime   : Thu Dec  3 11:14:51 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 114 expanded)
%              Number of clauses        :   33 (  41 expanded)
%              Number of leaves         :   10 (  33 expanded)
%              Depth                    :    5
%              Number of atoms          :  343 ( 912 expanded)
%              Number of equality atoms :   36 ( 102 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   28 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(commutativity_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(t18_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattices(X1,X2,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_lattices)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_filter_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(c_0_10,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ v4_lattices(X14)
      | ~ l2_lattices(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | k3_lattices(X14,X15,X16) = k1_lattices(X14,X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

fof(c_0_11,plain,(
    ! [X5,X6,X7] :
      ( v2_struct_0(X5)
      | ~ v4_lattices(X5)
      | ~ l2_lattices(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | k3_lattices(X5,X6,X7) = k3_lattices(X5,X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).

cnf(c_0_12,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k3_lattices(X1,X3,X2)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

fof(c_0_14,plain,(
    ! [X23,X24] :
      ( v2_struct_0(X23)
      | ~ v6_lattices(X23)
      | ~ v8_lattices(X23)
      | ~ v9_lattices(X23)
      | ~ l3_lattices(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | k4_lattices(X23,X24,X24) = X24 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t18_lattices])])])])).

fof(c_0_15,plain,(
    ! [X17,X18,X19] :
      ( v2_struct_0(X17)
      | ~ v6_lattices(X17)
      | ~ l1_lattices(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | k4_lattices(X17,X18,X19) = k2_lattices(X17,X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

fof(c_0_16,plain,(
    ! [X13] :
      ( ( l1_lattices(X13)
        | ~ l3_lattices(X13) )
      & ( l2_lattices(X13)
        | ~ l3_lattices(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_17,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v8_lattices(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | k1_lattices(X8,k2_lattices(X8,X9,X10),X10) = X10
        | v2_struct_0(X8)
        | ~ l3_lattices(X8) )
      & ( m1_subset_1(esk1_1(X8),u1_struct_0(X8))
        | v8_lattices(X8)
        | v2_struct_0(X8)
        | ~ l3_lattices(X8) )
      & ( m1_subset_1(esk2_1(X8),u1_struct_0(X8))
        | v8_lattices(X8)
        | v2_struct_0(X8)
        | ~ l3_lattices(X8) )
      & ( k1_lattices(X8,k2_lattices(X8,esk1_1(X8),esk2_1(X8)),esk2_1(X8)) != esk2_1(X8)
        | v8_lattices(X8)
        | v2_struct_0(X8)
        | ~ l3_lattices(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).

cnf(c_0_18,plain,
    ( k3_lattices(X1,X2,X3) = k1_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13]),
    [final]).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X2) = X2
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_21,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

fof(c_0_22,negated_conjecture,(
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

cnf(c_0_23,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_24,plain,
    ( k1_lattices(X1,X2,X3) = k1_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_18]),
    [final]).

cnf(c_0_25,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_26,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,esk1_1(X1),esk2_1(X1)),esk2_1(X1)) != esk2_1(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_27,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_28,plain,
    ( k2_lattices(X1,X2,X2) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),
    [final]).

fof(c_0_29,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r3_lattices(X20,X21,X22)
        | r1_lattices(X20,X21,X22)
        | v2_struct_0(X20)
        | ~ v6_lattices(X20)
        | ~ v8_lattices(X20)
        | ~ v9_lattices(X20)
        | ~ l3_lattices(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20)) )
      & ( ~ r1_lattices(X20,X21,X22)
        | r3_lattices(X20,X21,X22)
        | v2_struct_0(X20)
        | ~ v6_lattices(X20)
        | ~ v8_lattices(X20)
        | ~ v9_lattices(X20)
        | ~ l3_lattices(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

fof(c_0_30,plain,(
    ! [X25,X26,X27] :
      ( ( ~ r1_lattices(X25,X26,X27)
        | k2_lattices(X25,X26,X27) = X26
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | v2_struct_0(X25)
        | ~ v8_lattices(X25)
        | ~ v9_lattices(X25)
        | ~ l3_lattices(X25) )
      & ( k2_lattices(X25,X26,X27) != X26
        | r1_lattices(X25,X26,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | v2_struct_0(X25)
        | ~ v8_lattices(X25)
        | ~ v9_lattices(X25)
        | ~ l3_lattices(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

fof(c_0_31,plain,(
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

fof(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v10_lattices(esk3_0)
    & l3_lattices(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & k2_filter_0(esk3_0,esk4_0) = k2_filter_0(esk3_0,esk5_0)
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

cnf(c_0_33,plain,
    ( k1_lattices(X1,X2,k2_lattices(X1,X3,X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_lattices(X1,X3,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),
    [final]).

cnf(c_0_34,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,esk2_1(X1),k2_lattices(X1,esk1_1(X1),esk2_1(X1))) != esk2_1(X1)
    | ~ m1_subset_1(k2_lattices(X1,esk1_1(X1),esk2_1(X1)),u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_24]),c_0_25]),c_0_27]),
    [final]).

cnf(c_0_35,plain,
    ( k1_lattices(X1,X2,X2) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_28]),
    [final]).

cnf(c_0_36,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_37,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_38,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X3) != X2
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_39,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_40,plain,
    ( m1_subset_1(esk1_1(X1),u1_struct_0(X1))
    | v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_41,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_42,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_43,plain,
    ( v7_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_44,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_45,plain,
    ( v5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_46,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( k2_filter_0(esk3_0,esk4_0) = k2_filter_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( v10_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( l3_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.13/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.029 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # No proof found!
% 0.13/0.37  # SZS status CounterSatisfiable
% 0.13/0.37  # SZS output start Saturation
% 0.13/0.37  fof(redefinition_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 0.13/0.37  fof(commutativity_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 0.13/0.37  fof(t18_lattices, axiom, ![X1]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,X2,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_lattices)).
% 0.13/0.37  fof(redefinition_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 0.13/0.37  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.13/0.37  fof(d8_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v8_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 0.13/0.37  fof(t2_filter_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_filter_0(X1,X2)=k2_filter_0(X1,X3)=>X2=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_filter_1)).
% 0.13/0.37  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.13/0.37  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 0.13/0.37  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.13/0.37  fof(c_0_10, plain, ![X14, X15, X16]:(v2_struct_0(X14)|~v4_lattices(X14)|~l2_lattices(X14)|~m1_subset_1(X15,u1_struct_0(X14))|~m1_subset_1(X16,u1_struct_0(X14))|k3_lattices(X14,X15,X16)=k1_lattices(X14,X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).
% 0.13/0.37  fof(c_0_11, plain, ![X5, X6, X7]:(v2_struct_0(X5)|~v4_lattices(X5)|~l2_lattices(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))|k3_lattices(X5,X6,X7)=k3_lattices(X5,X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k3_lattices])])])).
% 0.13/0.37  cnf(c_0_12, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.37  cnf(c_0_13, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k3_lattices(X1,X3,X2)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.13/0.37  fof(c_0_14, plain, ![X23, X24]:(v2_struct_0(X23)|~v6_lattices(X23)|~v8_lattices(X23)|~v9_lattices(X23)|~l3_lattices(X23)|(~m1_subset_1(X24,u1_struct_0(X23))|k4_lattices(X23,X24,X24)=X24)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t18_lattices])])])])).
% 0.13/0.37  fof(c_0_15, plain, ![X17, X18, X19]:(v2_struct_0(X17)|~v6_lattices(X17)|~l1_lattices(X17)|~m1_subset_1(X18,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|k4_lattices(X17,X18,X19)=k2_lattices(X17,X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).
% 0.13/0.37  fof(c_0_16, plain, ![X13]:((l1_lattices(X13)|~l3_lattices(X13))&(l2_lattices(X13)|~l3_lattices(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.13/0.37  fof(c_0_17, plain, ![X8, X9, X10]:((~v8_lattices(X8)|(~m1_subset_1(X9,u1_struct_0(X8))|(~m1_subset_1(X10,u1_struct_0(X8))|k1_lattices(X8,k2_lattices(X8,X9,X10),X10)=X10))|(v2_struct_0(X8)|~l3_lattices(X8)))&((m1_subset_1(esk1_1(X8),u1_struct_0(X8))|v8_lattices(X8)|(v2_struct_0(X8)|~l3_lattices(X8)))&((m1_subset_1(esk2_1(X8),u1_struct_0(X8))|v8_lattices(X8)|(v2_struct_0(X8)|~l3_lattices(X8)))&(k1_lattices(X8,k2_lattices(X8,esk1_1(X8),esk2_1(X8)),esk2_1(X8))!=esk2_1(X8)|v8_lattices(X8)|(v2_struct_0(X8)|~l3_lattices(X8)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).
% 0.13/0.37  cnf(c_0_18, plain, (k3_lattices(X1,X2,X3)=k1_lattices(X1,X3,X2)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l2_lattices(X1)|~v4_lattices(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13]), ['final']).
% 0.13/0.37  cnf(c_0_19, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X2)=X2|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.13/0.37  cnf(c_0_20, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.37  cnf(c_0_21, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.13/0.37  fof(c_0_22, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_filter_0(X1,X2)=k2_filter_0(X1,X3)=>X2=X3))))), inference(assume_negation,[status(cth)],[t2_filter_1])).
% 0.13/0.37  cnf(c_0_23, plain, (k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3|v2_struct_0(X1)|~v8_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.37  cnf(c_0_24, plain, (k1_lattices(X1,X2,X3)=k1_lattices(X1,X3,X2)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l2_lattices(X1)|~v4_lattices(X1)), inference(spm,[status(thm)],[c_0_12, c_0_18]), ['final']).
% 0.13/0.37  cnf(c_0_25, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.13/0.37  cnf(c_0_26, plain, (v8_lattices(X1)|v2_struct_0(X1)|k1_lattices(X1,k2_lattices(X1,esk1_1(X1),esk2_1(X1)),esk2_1(X1))!=esk2_1(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.37  cnf(c_0_27, plain, (m1_subset_1(esk2_1(X1),u1_struct_0(X1))|v8_lattices(X1)|v2_struct_0(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.37  cnf(c_0_28, plain, (k2_lattices(X1,X2,X2)=X2|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v9_lattices(X1)|~v8_lattices(X1)|~v6_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), ['final']).
% 0.13/0.37  fof(c_0_29, plain, ![X20, X21, X22]:((~r3_lattices(X20,X21,X22)|r1_lattices(X20,X21,X22)|(v2_struct_0(X20)|~v6_lattices(X20)|~v8_lattices(X20)|~v9_lattices(X20)|~l3_lattices(X20)|~m1_subset_1(X21,u1_struct_0(X20))|~m1_subset_1(X22,u1_struct_0(X20))))&(~r1_lattices(X20,X21,X22)|r3_lattices(X20,X21,X22)|(v2_struct_0(X20)|~v6_lattices(X20)|~v8_lattices(X20)|~v9_lattices(X20)|~l3_lattices(X20)|~m1_subset_1(X21,u1_struct_0(X20))|~m1_subset_1(X22,u1_struct_0(X20))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.13/0.37  fof(c_0_30, plain, ![X25, X26, X27]:((~r1_lattices(X25,X26,X27)|k2_lattices(X25,X26,X27)=X26|~m1_subset_1(X27,u1_struct_0(X25))|~m1_subset_1(X26,u1_struct_0(X25))|(v2_struct_0(X25)|~v8_lattices(X25)|~v9_lattices(X25)|~l3_lattices(X25)))&(k2_lattices(X25,X26,X27)!=X26|r1_lattices(X25,X26,X27)|~m1_subset_1(X27,u1_struct_0(X25))|~m1_subset_1(X26,u1_struct_0(X25))|(v2_struct_0(X25)|~v8_lattices(X25)|~v9_lattices(X25)|~l3_lattices(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.13/0.37  fof(c_0_31, plain, ![X4]:(((((((~v2_struct_0(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))&(v4_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v5_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v6_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v7_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v8_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v9_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.13/0.37  fof(c_0_32, negated_conjecture, (((~v2_struct_0(esk3_0)&v10_lattices(esk3_0))&l3_lattices(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&(k2_filter_0(esk3_0,esk4_0)=k2_filter_0(esk3_0,esk5_0)&esk4_0!=esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).
% 0.13/0.37  cnf(c_0_33, plain, (k1_lattices(X1,X2,k2_lattices(X1,X3,X2))=X2|v2_struct_0(X1)|~m1_subset_1(k2_lattices(X1,X3,X2),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v8_lattices(X1)|~v4_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), ['final']).
% 0.13/0.37  cnf(c_0_34, plain, (v8_lattices(X1)|v2_struct_0(X1)|k1_lattices(X1,esk2_1(X1),k2_lattices(X1,esk1_1(X1),esk2_1(X1)))!=esk2_1(X1)|~m1_subset_1(k2_lattices(X1,esk1_1(X1),esk2_1(X1)),u1_struct_0(X1))|~v4_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_24]), c_0_25]), c_0_27]), ['final']).
% 0.13/0.37  cnf(c_0_35, plain, (k1_lattices(X1,X2,X2)=X2|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v9_lattices(X1)|~v8_lattices(X1)|~v6_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_23, c_0_28]), ['final']).
% 0.13/0.37  cnf(c_0_36, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.13/0.37  cnf(c_0_37, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.13/0.37  cnf(c_0_38, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k2_lattices(X1,X2,X3)!=X2|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.13/0.37  cnf(c_0_39, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.13/0.37  cnf(c_0_40, plain, (m1_subset_1(esk1_1(X1),u1_struct_0(X1))|v8_lattices(X1)|v2_struct_0(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.37  cnf(c_0_41, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.13/0.37  cnf(c_0_42, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.13/0.37  cnf(c_0_43, plain, (v7_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.13/0.37  cnf(c_0_44, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.13/0.37  cnf(c_0_45, plain, (v5_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.13/0.37  cnf(c_0_46, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.13/0.37  cnf(c_0_47, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.13/0.37  cnf(c_0_48, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.13/0.37  cnf(c_0_49, negated_conjecture, (k2_filter_0(esk3_0,esk4_0)=k2_filter_0(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.13/0.37  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.13/0.37  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.13/0.37  cnf(c_0_52, negated_conjecture, (v10_lattices(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.13/0.37  cnf(c_0_53, negated_conjecture, (l3_lattices(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.13/0.37  # SZS output end Saturation
% 0.13/0.37  # Proof object total steps             : 54
% 0.13/0.37  # Proof object clause steps            : 33
% 0.13/0.37  # Proof object formula steps           : 21
% 0.13/0.37  # Proof object conjectures             : 10
% 0.13/0.37  # Proof object clause conjectures      : 7
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 27
% 0.13/0.37  # Proof object initial formulas used   : 10
% 0.13/0.37  # Proof object generating inferences   : 6
% 0.13/0.37  # Proof object simplifying inferences  : 4
% 0.13/0.37  # Parsed axioms                        : 10
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 28
% 0.13/0.37  # Removed in clause preprocessing      : 1
% 0.13/0.37  # Initial clauses in saturation        : 27
% 0.13/0.37  # Processed clauses                    : 68
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 8
% 0.13/0.37  # ...remaining for further processing  : 60
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 18
% 0.13/0.37  # ...of the previous two non-trivial   : 14
% 0.13/0.37  # Contextual simplify-reflections      : 4
% 0.13/0.37  # Paramodulations                      : 18
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 33
% 0.13/0.37  #    Positive orientable unit clauses  : 5
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 26
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 27
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 555
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 108
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 12
% 0.13/0.37  # Unit Clause-clause subsumption calls : 0
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 0
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 3883
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.029 s
% 0.13/0.37  # System time              : 0.006 s
% 0.13/0.37  # Total time               : 0.036 s
% 0.13/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
