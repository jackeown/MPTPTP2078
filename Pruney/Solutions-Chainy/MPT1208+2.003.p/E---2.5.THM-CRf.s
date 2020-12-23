%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:27 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 839 expanded)
%              Number of clauses        :   59 ( 277 expanded)
%              Number of leaves         :   14 ( 207 expanded)
%              Depth                    :   13
%              Number of atoms          :  469 (4752 expanded)
%              Number of equality atoms :   42 ( 488 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v14_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattices(X1,k6_lattices(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).

fof(dt_k2_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

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

fof(t22_lattices,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_lattices)).

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

fof(dt_k6_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => m1_subset_1(k6_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(t27_lattices,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

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

fof(reflexivity_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_lattices(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

fof(d17_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ( v14_lattices(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( X2 = k6_lattices(X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( k1_lattices(X1,X2,X3) = X2
                    & k1_lattices(X1,X3,X2) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattices)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v14_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => k4_lattices(X1,k6_lattices(X1),X2) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t43_lattices])).

fof(c_0_15,plain,(
    ! [X22,X23,X24] :
      ( v2_struct_0(X22)
      | ~ l1_lattices(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | ~ m1_subset_1(X24,u1_struct_0(X22))
      | m1_subset_1(k2_lattices(X22,X23,X24),u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattices])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v10_lattices(esk7_0)
    & v14_lattices(esk7_0)
    & l3_lattices(esk7_0)
    & m1_subset_1(esk8_0,u1_struct_0(esk7_0))
    & k4_lattices(esk7_0,k6_lattices(esk7_0),esk8_0) != esk8_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X26] :
      ( ( l1_lattices(X26)
        | ~ l3_lattices(X26) )
      & ( l2_lattices(X26)
        | ~ l3_lattices(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_21,plain,(
    ! [X5] :
      ( ( ~ v2_struct_0(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v4_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v5_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v6_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v7_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v8_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) )
      & ( v9_lattices(X5)
        | v2_struct_0(X5)
        | ~ v10_lattices(X5)
        | ~ l3_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_22,plain,(
    ! [X42,X43,X44] :
      ( v2_struct_0(X42)
      | ~ v4_lattices(X42)
      | ~ l2_lattices(X42)
      | ~ m1_subset_1(X43,u1_struct_0(X42))
      | ~ m1_subset_1(X44,u1_struct_0(X42))
      | ~ r1_lattices(X42,X43,X44)
      | ~ r1_lattices(X42,X44,X43)
      | X43 = X44 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk7_0,X1,esk8_0),u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_24,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( l3_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( v10_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_28,plain,(
    ! [X39,X40,X41] :
      ( v2_struct_0(X39)
      | ~ v5_lattices(X39)
      | ~ v6_lattices(X39)
      | ~ v8_lattices(X39)
      | ~ v9_lattices(X39)
      | ~ l3_lattices(X39)
      | ~ m1_subset_1(X40,u1_struct_0(X39))
      | ~ m1_subset_1(X41,u1_struct_0(X39))
      | r1_lattices(X39,X40,k1_lattices(X39,X40,X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_lattices])])])])).

cnf(c_0_29,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_33,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v8_lattices(X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | k1_lattices(X17,k2_lattices(X17,X18,X19),X19) = X19
        | v2_struct_0(X17)
        | ~ l3_lattices(X17) )
      & ( m1_subset_1(esk5_1(X17),u1_struct_0(X17))
        | v8_lattices(X17)
        | v2_struct_0(X17)
        | ~ l3_lattices(X17) )
      & ( m1_subset_1(esk6_1(X17),u1_struct_0(X17))
        | v8_lattices(X17)
        | v2_struct_0(X17)
        | ~ l3_lattices(X17) )
      & ( k1_lattices(X17,k2_lattices(X17,esk5_1(X17),esk6_1(X17)),esk6_1(X17)) != esk6_1(X17)
        | v8_lattices(X17)
        | v2_struct_0(X17)
        | ~ l3_lattices(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).

fof(c_0_34,plain,(
    ! [X25] :
      ( v2_struct_0(X25)
      | ~ l2_lattices(X25)
      | m1_subset_1(k6_lattices(X25),u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_lattices])])])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk7_0,X1,esk8_0),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_37,negated_conjecture,
    ( v4_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_25])]),c_0_19])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,X2,k1_lattices(X1,X2,X3))
    | ~ v5_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( v9_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_27]),c_0_25])]),c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( v8_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_27]),c_0_25])]),c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_27]),c_0_25])]),c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( v5_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_25])]),c_0_19])).

cnf(c_0_43,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_44,plain,(
    ! [X45,X46,X47,X48] :
      ( v2_struct_0(X45)
      | ~ v7_lattices(X45)
      | ~ v8_lattices(X45)
      | ~ v9_lattices(X45)
      | ~ l3_lattices(X45)
      | ~ m1_subset_1(X46,u1_struct_0(X45))
      | ~ m1_subset_1(X47,u1_struct_0(X45))
      | ~ m1_subset_1(X48,u1_struct_0(X45))
      | ~ r1_lattices(X45,X46,X47)
      | r1_lattices(X45,k2_lattices(X45,X46,X48),k2_lattices(X45,X47,X48)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_lattices])])])])).

cnf(c_0_45,plain,
    ( v7_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_46,plain,(
    ! [X36,X37,X38] :
      ( ( ~ r1_lattices(X36,X37,X38)
        | k2_lattices(X36,X37,X38) = X37
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v8_lattices(X36)
        | ~ v9_lattices(X36)
        | ~ l3_lattices(X36) )
      & ( k2_lattices(X36,X37,X38) != X37
        | r1_lattices(X36,X37,X38)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v8_lattices(X36)
        | ~ v9_lattices(X36)
        | ~ l3_lattices(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

fof(c_0_47,plain,(
    ! [X30,X31,X32] :
      ( ( ~ r3_lattices(X30,X31,X32)
        | r1_lattices(X30,X31,X32)
        | v2_struct_0(X30)
        | ~ v6_lattices(X30)
        | ~ v8_lattices(X30)
        | ~ v9_lattices(X30)
        | ~ l3_lattices(X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(X30)) )
      & ( ~ r1_lattices(X30,X31,X32)
        | r3_lattices(X30,X31,X32)
        | v2_struct_0(X30)
        | ~ v6_lattices(X30)
        | ~ v8_lattices(X30)
        | ~ v9_lattices(X30)
        | ~ l3_lattices(X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

fof(c_0_48,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ v6_lattices(X33)
      | ~ v8_lattices(X33)
      | ~ v9_lattices(X33)
      | ~ l3_lattices(X33)
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | ~ m1_subset_1(X35,u1_struct_0(X33))
      | r3_lattices(X33,X34,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_lattices])])])).

fof(c_0_49,plain,(
    ! [X6,X7,X8] :
      ( ( k1_lattices(X6,X7,X8) = X7
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | X7 != k6_lattices(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v14_lattices(X6)
        | v2_struct_0(X6)
        | ~ l2_lattices(X6) )
      & ( k1_lattices(X6,X8,X7) = X7
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | X7 != k6_lattices(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v14_lattices(X6)
        | v2_struct_0(X6)
        | ~ l2_lattices(X6) )
      & ( m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))
        | X7 = k6_lattices(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v14_lattices(X6)
        | v2_struct_0(X6)
        | ~ l2_lattices(X6) )
      & ( k1_lattices(X6,X7,esk1_2(X6,X7)) != X7
        | k1_lattices(X6,esk1_2(X6,X7),X7) != X7
        | X7 = k6_lattices(X6)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ v14_lattices(X6)
        | v2_struct_0(X6)
        | ~ l2_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattices])])])])])])).

fof(c_0_50,plain,(
    ! [X27,X28,X29] :
      ( v2_struct_0(X27)
      | ~ v6_lattices(X27)
      | ~ l1_lattices(X27)
      | ~ m1_subset_1(X28,u1_struct_0(X27))
      | ~ m1_subset_1(X29,u1_struct_0(X27))
      | k4_lattices(X27,X28,X29) = k2_lattices(X27,X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_52,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_53,negated_conjecture,
    ( X1 = k2_lattices(esk7_0,X2,esk8_0)
    | ~ r1_lattices(esk7_0,k2_lattices(esk7_0,X2,esk8_0),X1)
    | ~ r1_lattices(esk7_0,X1,k2_lattices(esk7_0,X2,esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ l2_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])]),c_0_19])).

cnf(c_0_54,negated_conjecture,
    ( r1_lattices(esk7_0,X1,k1_lattices(esk7_0,X1,esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_18]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_25])]),c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( k1_lattices(esk7_0,k2_lattices(esk7_0,X1,esk8_0),esk8_0) = esk8_0
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_18]),c_0_40]),c_0_25])]),c_0_19])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4))
    | ~ v7_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_57,negated_conjecture,
    ( v7_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_27]),c_0_25])]),c_0_19])).

cnf(c_0_58,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,X2,X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k6_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v14_lattices(X1)
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,plain,
    ( m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( X1 = k2_lattices(esk7_0,X2,esk8_0)
    | ~ r1_lattices(esk7_0,k2_lattices(esk7_0,X2,esk8_0),X1)
    | ~ r1_lattices(esk7_0,X1,k2_lattices(esk7_0,X2,esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_52]),c_0_25])])).

cnf(c_0_65,negated_conjecture,
    ( r1_lattices(esk7_0,k2_lattices(esk7_0,X1,esk8_0),esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_36])).

cnf(c_0_66,negated_conjecture,
    ( r1_lattices(esk7_0,k2_lattices(esk7_0,X1,esk8_0),k2_lattices(esk7_0,X2,esk8_0))
    | ~ r1_lattices(esk7_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_18]),c_0_39]),c_0_40]),c_0_57]),c_0_25])]),c_0_19])).

cnf(c_0_67,negated_conjecture,
    ( k2_lattices(esk7_0,X1,esk8_0) = X1
    | ~ r1_lattices(esk7_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_18]),c_0_39]),c_0_40]),c_0_25])]),c_0_19])).

cnf(c_0_68,negated_conjecture,
    ( r1_lattices(esk7_0,X1,esk8_0)
    | ~ r3_lattices(esk7_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_18]),c_0_39]),c_0_40]),c_0_41]),c_0_25])]),c_0_19])).

cnf(c_0_69,negated_conjecture,
    ( r3_lattices(esk7_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_18]),c_0_39]),c_0_40]),c_0_41]),c_0_25])]),c_0_19])).

cnf(c_0_70,plain,
    ( k1_lattices(X1,X2,k6_lattices(X1)) = k6_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v14_lattices(X1)
    | ~ l2_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_61]),c_0_51])).

cnf(c_0_71,negated_conjecture,
    ( v14_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_72,negated_conjecture,
    ( k4_lattices(esk7_0,k6_lattices(esk7_0),esk8_0) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_73,negated_conjecture,
    ( k4_lattices(esk7_0,X1,esk8_0) = k2_lattices(esk7_0,X1,esk8_0)
    | ~ l1_lattices(esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_18]),c_0_41])]),c_0_19])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(k6_lattices(esk7_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_25]),c_0_19])).

cnf(c_0_75,negated_conjecture,
    ( k2_lattices(esk7_0,X1,esk8_0) = esk8_0
    | ~ r1_lattices(esk7_0,esk8_0,k2_lattices(esk7_0,X1,esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_18])])).

cnf(c_0_76,negated_conjecture,
    ( r1_lattices(esk7_0,X1,k2_lattices(esk7_0,X2,esk8_0))
    | ~ r1_lattices(esk7_0,X1,esk8_0)
    | ~ r1_lattices(esk7_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( r1_lattices(esk7_0,esk8_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_18])])).

cnf(c_0_78,negated_conjecture,
    ( k1_lattices(esk7_0,k2_lattices(esk7_0,X1,esk8_0),k6_lattices(esk7_0)) = k6_lattices(esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ l2_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_36]),c_0_71])]),c_0_19])).

cnf(c_0_79,negated_conjecture,
    ( k2_lattices(esk7_0,k6_lattices(esk7_0),esk8_0) != esk8_0
    | ~ l1_lattices(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])])).

cnf(c_0_80,negated_conjecture,
    ( k2_lattices(esk7_0,X1,esk8_0) = esk8_0
    | ~ r1_lattices(esk7_0,esk8_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_18])])).

cnf(c_0_81,negated_conjecture,
    ( r1_lattices(esk7_0,X1,k1_lattices(esk7_0,X1,k6_lattices(esk7_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_74]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_25])]),c_0_19])).

cnf(c_0_82,negated_conjecture,
    ( k1_lattices(esk7_0,X1,k6_lattices(esk7_0)) = k6_lattices(esk7_0)
    | ~ r1_lattices(esk7_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ l2_lattices(esk7_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_67])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_lattices(esk7_0,esk8_0,k6_lattices(esk7_0))
    | ~ l1_lattices(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_74])])).

cnf(c_0_84,negated_conjecture,
    ( r1_lattices(esk7_0,X1,k6_lattices(esk7_0))
    | ~ r1_lattices(esk7_0,X1,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ l2_lattices(esk7_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( ~ l1_lattices(esk7_0)
    | ~ l2_lattices(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_77]),c_0_18])])).

cnf(c_0_86,negated_conjecture,
    ( ~ l2_lattices(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_24]),c_0_25])])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_52]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.45  #
% 0.21/0.45  # Preprocessing time       : 0.031 s
% 0.21/0.45  # Presaturation interreduction done
% 0.21/0.45  
% 0.21/0.45  # Proof found!
% 0.21/0.45  # SZS status Theorem
% 0.21/0.45  # SZS output start CNFRefutation
% 0.21/0.45  fof(t43_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v14_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,k6_lattices(X1),X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_lattices)).
% 0.21/0.45  fof(dt_k2_lattices, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_lattices)).
% 0.21/0.45  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.21/0.45  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.21/0.46  fof(t26_lattices, axiom, ![X1]:(((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_lattices(X1,X2,X3)&r1_lattices(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_lattices)).
% 0.21/0.46  fof(t22_lattices, axiom, ![X1]:((((((~(v2_struct_0(X1))&v5_lattices(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>r1_lattices(X1,X2,k1_lattices(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_lattices)).
% 0.21/0.46  fof(d8_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v8_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattices)).
% 0.21/0.46  fof(dt_k6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>m1_subset_1(k6_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_lattices)).
% 0.21/0.46  fof(t27_lattices, axiom, ![X1]:(((((~(v2_struct_0(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)=>r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_lattices)).
% 0.21/0.46  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 0.21/0.46  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.21/0.46  fof(reflexivity_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_lattices(X1,X2,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_lattices)).
% 0.21/0.46  fof(d17_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>(v14_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k6_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k1_lattices(X1,X2,X3)=X2&k1_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattices)).
% 0.21/0.46  fof(redefinition_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 0.21/0.46  fof(c_0_14, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v14_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,k6_lattices(X1),X2)=X2))), inference(assume_negation,[status(cth)],[t43_lattices])).
% 0.21/0.46  fof(c_0_15, plain, ![X22, X23, X24]:(v2_struct_0(X22)|~l1_lattices(X22)|~m1_subset_1(X23,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|m1_subset_1(k2_lattices(X22,X23,X24),u1_struct_0(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattices])])])).
% 0.21/0.46  fof(c_0_16, negated_conjecture, ((((~v2_struct_0(esk7_0)&v10_lattices(esk7_0))&v14_lattices(esk7_0))&l3_lattices(esk7_0))&(m1_subset_1(esk8_0,u1_struct_0(esk7_0))&k4_lattices(esk7_0,k6_lattices(esk7_0),esk8_0)!=esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.21/0.46  cnf(c_0_17, plain, (v2_struct_0(X1)|m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.46  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.46  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.46  fof(c_0_20, plain, ![X26]:((l1_lattices(X26)|~l3_lattices(X26))&(l2_lattices(X26)|~l3_lattices(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.21/0.46  fof(c_0_21, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.21/0.46  fof(c_0_22, plain, ![X42, X43, X44]:(v2_struct_0(X42)|~v4_lattices(X42)|~l2_lattices(X42)|(~m1_subset_1(X43,u1_struct_0(X42))|(~m1_subset_1(X44,u1_struct_0(X42))|(~r1_lattices(X42,X43,X44)|~r1_lattices(X42,X44,X43)|X43=X44)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).
% 0.21/0.46  cnf(c_0_23, negated_conjecture, (m1_subset_1(k2_lattices(esk7_0,X1,esk8_0),u1_struct_0(esk7_0))|~l1_lattices(esk7_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.21/0.46  cnf(c_0_24, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.46  cnf(c_0_25, negated_conjecture, (l3_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.46  cnf(c_0_26, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.46  cnf(c_0_27, negated_conjecture, (v10_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.46  fof(c_0_28, plain, ![X39, X40, X41]:(v2_struct_0(X39)|~v5_lattices(X39)|~v6_lattices(X39)|~v8_lattices(X39)|~v9_lattices(X39)|~l3_lattices(X39)|(~m1_subset_1(X40,u1_struct_0(X39))|(~m1_subset_1(X41,u1_struct_0(X39))|r1_lattices(X39,X40,k1_lattices(X39,X40,X41))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_lattices])])])])).
% 0.21/0.46  cnf(c_0_29, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.46  cnf(c_0_30, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.46  cnf(c_0_31, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.46  cnf(c_0_32, plain, (v5_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.46  fof(c_0_33, plain, ![X17, X18, X19]:((~v8_lattices(X17)|(~m1_subset_1(X18,u1_struct_0(X17))|(~m1_subset_1(X19,u1_struct_0(X17))|k1_lattices(X17,k2_lattices(X17,X18,X19),X19)=X19))|(v2_struct_0(X17)|~l3_lattices(X17)))&((m1_subset_1(esk5_1(X17),u1_struct_0(X17))|v8_lattices(X17)|(v2_struct_0(X17)|~l3_lattices(X17)))&((m1_subset_1(esk6_1(X17),u1_struct_0(X17))|v8_lattices(X17)|(v2_struct_0(X17)|~l3_lattices(X17)))&(k1_lattices(X17,k2_lattices(X17,esk5_1(X17),esk6_1(X17)),esk6_1(X17))!=esk6_1(X17)|v8_lattices(X17)|(v2_struct_0(X17)|~l3_lattices(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).
% 0.21/0.46  fof(c_0_34, plain, ![X25]:(v2_struct_0(X25)|~l2_lattices(X25)|m1_subset_1(k6_lattices(X25),u1_struct_0(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_lattices])])])).
% 0.21/0.46  cnf(c_0_35, plain, (v2_struct_0(X1)|X2=X3|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattices(X1,X2,X3)|~r1_lattices(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.46  cnf(c_0_36, negated_conjecture, (m1_subset_1(k2_lattices(esk7_0,X1,esk8_0),u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.21/0.46  cnf(c_0_37, negated_conjecture, (v4_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_25])]), c_0_19])).
% 0.21/0.46  cnf(c_0_38, plain, (v2_struct_0(X1)|r1_lattices(X1,X2,k1_lattices(X1,X2,X3))|~v5_lattices(X1)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.46  cnf(c_0_39, negated_conjecture, (v9_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_27]), c_0_25])]), c_0_19])).
% 0.21/0.46  cnf(c_0_40, negated_conjecture, (v8_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_27]), c_0_25])]), c_0_19])).
% 0.21/0.46  cnf(c_0_41, negated_conjecture, (v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_27]), c_0_25])]), c_0_19])).
% 0.21/0.46  cnf(c_0_42, negated_conjecture, (v5_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_27]), c_0_25])]), c_0_19])).
% 0.21/0.46  cnf(c_0_43, plain, (k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3|v2_struct_0(X1)|~v8_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.46  fof(c_0_44, plain, ![X45, X46, X47, X48]:(v2_struct_0(X45)|~v7_lattices(X45)|~v8_lattices(X45)|~v9_lattices(X45)|~l3_lattices(X45)|(~m1_subset_1(X46,u1_struct_0(X45))|(~m1_subset_1(X47,u1_struct_0(X45))|(~m1_subset_1(X48,u1_struct_0(X45))|(~r1_lattices(X45,X46,X47)|r1_lattices(X45,k2_lattices(X45,X46,X48),k2_lattices(X45,X47,X48))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_lattices])])])])).
% 0.21/0.46  cnf(c_0_45, plain, (v7_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.46  fof(c_0_46, plain, ![X36, X37, X38]:((~r1_lattices(X36,X37,X38)|k2_lattices(X36,X37,X38)=X37|~m1_subset_1(X38,u1_struct_0(X36))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~v8_lattices(X36)|~v9_lattices(X36)|~l3_lattices(X36)))&(k2_lattices(X36,X37,X38)!=X37|r1_lattices(X36,X37,X38)|~m1_subset_1(X38,u1_struct_0(X36))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~v8_lattices(X36)|~v9_lattices(X36)|~l3_lattices(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.21/0.46  fof(c_0_47, plain, ![X30, X31, X32]:((~r3_lattices(X30,X31,X32)|r1_lattices(X30,X31,X32)|(v2_struct_0(X30)|~v6_lattices(X30)|~v8_lattices(X30)|~v9_lattices(X30)|~l3_lattices(X30)|~m1_subset_1(X31,u1_struct_0(X30))|~m1_subset_1(X32,u1_struct_0(X30))))&(~r1_lattices(X30,X31,X32)|r3_lattices(X30,X31,X32)|(v2_struct_0(X30)|~v6_lattices(X30)|~v8_lattices(X30)|~v9_lattices(X30)|~l3_lattices(X30)|~m1_subset_1(X31,u1_struct_0(X30))|~m1_subset_1(X32,u1_struct_0(X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.21/0.46  fof(c_0_48, plain, ![X33, X34, X35]:(v2_struct_0(X33)|~v6_lattices(X33)|~v8_lattices(X33)|~v9_lattices(X33)|~l3_lattices(X33)|~m1_subset_1(X34,u1_struct_0(X33))|~m1_subset_1(X35,u1_struct_0(X33))|r3_lattices(X33,X34,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_lattices])])])).
% 0.21/0.46  fof(c_0_49, plain, ![X6, X7, X8]:(((k1_lattices(X6,X7,X8)=X7|~m1_subset_1(X8,u1_struct_0(X6))|X7!=k6_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~v14_lattices(X6)|(v2_struct_0(X6)|~l2_lattices(X6)))&(k1_lattices(X6,X8,X7)=X7|~m1_subset_1(X8,u1_struct_0(X6))|X7!=k6_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~v14_lattices(X6)|(v2_struct_0(X6)|~l2_lattices(X6))))&((m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))|X7=k6_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~v14_lattices(X6)|(v2_struct_0(X6)|~l2_lattices(X6)))&(k1_lattices(X6,X7,esk1_2(X6,X7))!=X7|k1_lattices(X6,esk1_2(X6,X7),X7)!=X7|X7=k6_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~v14_lattices(X6)|(v2_struct_0(X6)|~l2_lattices(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattices])])])])])])).
% 0.21/0.46  fof(c_0_50, plain, ![X27, X28, X29]:(v2_struct_0(X27)|~v6_lattices(X27)|~l1_lattices(X27)|~m1_subset_1(X28,u1_struct_0(X27))|~m1_subset_1(X29,u1_struct_0(X27))|k4_lattices(X27,X28,X29)=k2_lattices(X27,X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).
% 0.21/0.46  cnf(c_0_51, plain, (v2_struct_0(X1)|m1_subset_1(k6_lattices(X1),u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.46  cnf(c_0_52, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.46  cnf(c_0_53, negated_conjecture, (X1=k2_lattices(esk7_0,X2,esk8_0)|~r1_lattices(esk7_0,k2_lattices(esk7_0,X2,esk8_0),X1)|~r1_lattices(esk7_0,X1,k2_lattices(esk7_0,X2,esk8_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~m1_subset_1(X2,u1_struct_0(esk7_0))|~l2_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])]), c_0_19])).
% 0.21/0.46  cnf(c_0_54, negated_conjecture, (r1_lattices(esk7_0,X1,k1_lattices(esk7_0,X1,esk8_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_18]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_25])]), c_0_19])).
% 0.21/0.46  cnf(c_0_55, negated_conjecture, (k1_lattices(esk7_0,k2_lattices(esk7_0,X1,esk8_0),esk8_0)=esk8_0|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_18]), c_0_40]), c_0_25])]), c_0_19])).
% 0.21/0.46  cnf(c_0_56, plain, (v2_struct_0(X1)|r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4))|~v7_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~r1_lattices(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.46  cnf(c_0_57, negated_conjecture, (v7_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_27]), c_0_25])]), c_0_19])).
% 0.21/0.46  cnf(c_0_58, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.46  cnf(c_0_59, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.46  cnf(c_0_60, plain, (v2_struct_0(X1)|r3_lattices(X1,X2,X2)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.46  cnf(c_0_61, plain, (k1_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k6_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v14_lattices(X1)|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.46  cnf(c_0_62, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.46  cnf(c_0_63, plain, (m1_subset_1(k6_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.46  cnf(c_0_64, negated_conjecture, (X1=k2_lattices(esk7_0,X2,esk8_0)|~r1_lattices(esk7_0,k2_lattices(esk7_0,X2,esk8_0),X1)|~r1_lattices(esk7_0,X1,k2_lattices(esk7_0,X2,esk8_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~m1_subset_1(X2,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_52]), c_0_25])])).
% 0.21/0.46  cnf(c_0_65, negated_conjecture, (r1_lattices(esk7_0,k2_lattices(esk7_0,X1,esk8_0),esk8_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_36])).
% 0.21/0.46  cnf(c_0_66, negated_conjecture, (r1_lattices(esk7_0,k2_lattices(esk7_0,X1,esk8_0),k2_lattices(esk7_0,X2,esk8_0))|~r1_lattices(esk7_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_18]), c_0_39]), c_0_40]), c_0_57]), c_0_25])]), c_0_19])).
% 0.21/0.46  cnf(c_0_67, negated_conjecture, (k2_lattices(esk7_0,X1,esk8_0)=X1|~r1_lattices(esk7_0,X1,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_18]), c_0_39]), c_0_40]), c_0_25])]), c_0_19])).
% 0.21/0.46  cnf(c_0_68, negated_conjecture, (r1_lattices(esk7_0,X1,esk8_0)|~r3_lattices(esk7_0,X1,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_18]), c_0_39]), c_0_40]), c_0_41]), c_0_25])]), c_0_19])).
% 0.21/0.46  cnf(c_0_69, negated_conjecture, (r3_lattices(esk7_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_18]), c_0_39]), c_0_40]), c_0_41]), c_0_25])]), c_0_19])).
% 0.21/0.46  cnf(c_0_70, plain, (k1_lattices(X1,X2,k6_lattices(X1))=k6_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v14_lattices(X1)|~l2_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_61]), c_0_51])).
% 0.21/0.46  cnf(c_0_71, negated_conjecture, (v14_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.46  cnf(c_0_72, negated_conjecture, (k4_lattices(esk7_0,k6_lattices(esk7_0),esk8_0)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.46  cnf(c_0_73, negated_conjecture, (k4_lattices(esk7_0,X1,esk8_0)=k2_lattices(esk7_0,X1,esk8_0)|~l1_lattices(esk7_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_18]), c_0_41])]), c_0_19])).
% 0.21/0.46  cnf(c_0_74, negated_conjecture, (m1_subset_1(k6_lattices(esk7_0),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_25]), c_0_19])).
% 0.21/0.46  cnf(c_0_75, negated_conjecture, (k2_lattices(esk7_0,X1,esk8_0)=esk8_0|~r1_lattices(esk7_0,esk8_0,k2_lattices(esk7_0,X1,esk8_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_18])])).
% 0.21/0.46  cnf(c_0_76, negated_conjecture, (r1_lattices(esk7_0,X1,k2_lattices(esk7_0,X2,esk8_0))|~r1_lattices(esk7_0,X1,esk8_0)|~r1_lattices(esk7_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.21/0.46  cnf(c_0_77, negated_conjecture, (r1_lattices(esk7_0,esk8_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_18])])).
% 0.21/0.46  cnf(c_0_78, negated_conjecture, (k1_lattices(esk7_0,k2_lattices(esk7_0,X1,esk8_0),k6_lattices(esk7_0))=k6_lattices(esk7_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))|~l2_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_36]), c_0_71])]), c_0_19])).
% 0.21/0.46  cnf(c_0_79, negated_conjecture, (k2_lattices(esk7_0,k6_lattices(esk7_0),esk8_0)!=esk8_0|~l1_lattices(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])])).
% 0.21/0.46  cnf(c_0_80, negated_conjecture, (k2_lattices(esk7_0,X1,esk8_0)=esk8_0|~r1_lattices(esk7_0,esk8_0,X1)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_18])])).
% 0.21/0.46  cnf(c_0_81, negated_conjecture, (r1_lattices(esk7_0,X1,k1_lattices(esk7_0,X1,k6_lattices(esk7_0)))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_74]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_25])]), c_0_19])).
% 0.21/0.46  cnf(c_0_82, negated_conjecture, (k1_lattices(esk7_0,X1,k6_lattices(esk7_0))=k6_lattices(esk7_0)|~r1_lattices(esk7_0,X1,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))|~l2_lattices(esk7_0)), inference(spm,[status(thm)],[c_0_78, c_0_67])).
% 0.21/0.46  cnf(c_0_83, negated_conjecture, (~r1_lattices(esk7_0,esk8_0,k6_lattices(esk7_0))|~l1_lattices(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_74])])).
% 0.21/0.46  cnf(c_0_84, negated_conjecture, (r1_lattices(esk7_0,X1,k6_lattices(esk7_0))|~r1_lattices(esk7_0,X1,esk8_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))|~l2_lattices(esk7_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.21/0.46  cnf(c_0_85, negated_conjecture, (~l1_lattices(esk7_0)|~l2_lattices(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_77]), c_0_18])])).
% 0.21/0.46  cnf(c_0_86, negated_conjecture, (~l2_lattices(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_24]), c_0_25])])).
% 0.21/0.46  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_52]), c_0_25])]), ['proof']).
% 0.21/0.46  # SZS output end CNFRefutation
% 0.21/0.46  # Proof object total steps             : 88
% 0.21/0.46  # Proof object clause steps            : 59
% 0.21/0.46  # Proof object formula steps           : 29
% 0.21/0.46  # Proof object conjectures             : 41
% 0.21/0.46  # Proof object clause conjectures      : 38
% 0.21/0.46  # Proof object formula conjectures     : 3
% 0.21/0.46  # Proof object initial clauses used    : 25
% 0.21/0.46  # Proof object initial formulas used   : 14
% 0.21/0.46  # Proof object generating inferences   : 33
% 0.21/0.46  # Proof object simplifying inferences  : 95
% 0.21/0.46  # Training examples: 0 positive, 0 negative
% 0.21/0.46  # Parsed axioms                        : 15
% 0.21/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.46  # Initial clauses                      : 39
% 0.21/0.46  # Removed in clause preprocessing      : 1
% 0.21/0.46  # Initial clauses in saturation        : 38
% 0.21/0.46  # Processed clauses                    : 619
% 0.21/0.46  # ...of these trivial                  : 0
% 0.21/0.46  # ...subsumed                          : 211
% 0.21/0.46  # ...remaining for further processing  : 408
% 0.21/0.46  # Other redundant clauses eliminated   : 4
% 0.21/0.46  # Clauses deleted for lack of memory   : 0
% 0.21/0.46  # Backward-subsumed                    : 62
% 0.21/0.46  # Backward-rewritten                   : 0
% 0.21/0.46  # Generated clauses                    : 2248
% 0.21/0.46  # ...of the previous two non-trivial   : 2093
% 0.21/0.46  # Contextual simplify-reflections      : 24
% 0.21/0.46  # Paramodulations                      : 2244
% 0.21/0.46  # Factorizations                       : 0
% 0.21/0.46  # Equation resolutions                 : 4
% 0.21/0.46  # Propositional unsat checks           : 0
% 0.21/0.46  #    Propositional check models        : 0
% 0.21/0.46  #    Propositional check unsatisfiable : 0
% 0.21/0.46  #    Propositional clauses             : 0
% 0.21/0.46  #    Propositional clauses after purity: 0
% 0.21/0.46  #    Propositional unsat core size     : 0
% 0.21/0.46  #    Propositional preprocessing time  : 0.000
% 0.21/0.46  #    Propositional encoding time       : 0.000
% 0.21/0.46  #    Propositional solver time         : 0.000
% 0.21/0.46  #    Success case prop preproc time    : 0.000
% 0.21/0.46  #    Success case prop encoding time   : 0.000
% 0.21/0.46  #    Success case prop solver time     : 0.000
% 0.21/0.46  # Current number of processed clauses  : 306
% 0.21/0.46  #    Positive orientable unit clauses  : 15
% 0.21/0.46  #    Positive unorientable unit clauses: 0
% 0.21/0.46  #    Negative unit clauses             : 3
% 0.21/0.46  #    Non-unit-clauses                  : 288
% 0.21/0.46  # Current number of unprocessed clauses: 1546
% 0.21/0.46  # ...number of literals in the above   : 5427
% 0.21/0.46  # Current number of archived formulas  : 0
% 0.21/0.46  # Current number of archived clauses   : 100
% 0.21/0.46  # Clause-clause subsumption calls (NU) : 24876
% 0.21/0.46  # Rec. Clause-clause subsumption calls : 10141
% 0.21/0.46  # Non-unit clause-clause subsumptions  : 296
% 0.21/0.46  # Unit Clause-clause subsumption calls : 287
% 0.21/0.46  # Rewrite failures with RHS unbound    : 0
% 0.21/0.46  # BW rewrite match attempts            : 10
% 0.21/0.46  # BW rewrite match successes           : 1
% 0.21/0.46  # Condensation attempts                : 0
% 0.21/0.46  # Condensation successes               : 0
% 0.21/0.46  # Termbank termtop insertions          : 76986
% 0.21/0.46  
% 0.21/0.46  # -------------------------------------------------
% 0.21/0.46  # User time                : 0.110 s
% 0.21/0.46  # System time              : 0.004 s
% 0.21/0.46  # Total time               : 0.114 s
% 0.21/0.46  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
