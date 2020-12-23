%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:27 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 683 expanded)
%              Number of clauses        :   61 ( 229 expanded)
%              Number of leaves         :   14 ( 168 expanded)
%              Depth                    :   15
%              Number of atoms          :  474 (3742 expanded)
%              Number of equality atoms :   56 ( 418 expanded)
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

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

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

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v10_lattices(esk6_0)
    & v14_lattices(esk6_0)
    & l3_lattices(esk6_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & k4_lattices(esk6_0,k6_lattices(esk6_0),esk7_0) != esk7_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_17,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r3_lattices(X28,X29,X30)
        | r1_lattices(X28,X29,X30)
        | v2_struct_0(X28)
        | ~ v6_lattices(X28)
        | ~ v8_lattices(X28)
        | ~ v9_lattices(X28)
        | ~ l3_lattices(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ m1_subset_1(X30,u1_struct_0(X28)) )
      & ( ~ r1_lattices(X28,X29,X30)
        | r3_lattices(X28,X29,X30)
        | v2_struct_0(X28)
        | ~ v6_lattices(X28)
        | ~ v8_lattices(X28)
        | ~ v9_lattices(X28)
        | ~ l3_lattices(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ m1_subset_1(X30,u1_struct_0(X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_18,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v10_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( l3_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ v6_lattices(X31)
      | ~ v8_lattices(X31)
      | ~ v9_lattices(X31)
      | ~ l3_lattices(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | ~ m1_subset_1(X33,u1_struct_0(X31))
      | r3_lattices(X31,X32,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_lattices])])])).

fof(c_0_25,plain,(
    ! [X34,X35,X36] :
      ( ( ~ r1_lattices(X34,X35,X36)
        | k2_lattices(X34,X35,X36) = X35
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v8_lattices(X34)
        | ~ v9_lattices(X34)
        | ~ l3_lattices(X34) )
      & ( k2_lattices(X34,X35,X36) != X35
        | r1_lattices(X34,X35,X36)
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v8_lattices(X34)
        | ~ v9_lattices(X34)
        | ~ l3_lattices(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_26,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( v9_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v8_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v6_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,X2,X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X37,X38,X39] :
      ( v2_struct_0(X37)
      | ~ v4_lattices(X37)
      | ~ l2_lattices(X37)
      | ~ m1_subset_1(X38,u1_struct_0(X37))
      | ~ m1_subset_1(X39,u1_struct_0(X37))
      | ~ r1_lattices(X37,X38,X39)
      | ~ r1_lattices(X37,X39,X38)
      | X38 = X39 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

cnf(c_0_33,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_34,plain,(
    ! [X40,X41,X42,X43] :
      ( v2_struct_0(X40)
      | ~ v7_lattices(X40)
      | ~ v8_lattices(X40)
      | ~ v9_lattices(X40)
      | ~ l3_lattices(X40)
      | ~ m1_subset_1(X41,u1_struct_0(X40))
      | ~ m1_subset_1(X42,u1_struct_0(X40))
      | ~ m1_subset_1(X43,u1_struct_0(X40))
      | ~ r1_lattices(X40,X41,X42)
      | r1_lattices(X40,k2_lattices(X40,X41,X43),k2_lattices(X40,X42,X43)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_lattices])])])])).

cnf(c_0_35,plain,
    ( v7_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( r1_lattices(esk6_0,X1,esk7_0)
    | ~ r3_lattices(esk6_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_20])]),c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( r3_lattices(esk6_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_20])]),c_0_21])).

fof(c_0_39,plain,(
    ! [X20,X21,X22] :
      ( v2_struct_0(X20)
      | ~ l1_lattices(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | ~ m1_subset_1(X22,u1_struct_0(X20))
      | m1_subset_1(k2_lattices(X20,X21,X22),u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattices])])])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( v4_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_19]),c_0_20])]),c_0_21])).

fof(c_0_42,plain,(
    ! [X24] :
      ( ( l1_lattices(X24)
        | ~ l3_lattices(X24) )
      & ( l2_lattices(X24)
        | ~ l3_lattices(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_43,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( v7_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( k2_lattices(esk6_0,X1,esk7_0) = X1
    | ~ r1_lattices(esk6_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_27]),c_0_28]),c_0_29]),c_0_20])]),c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( r1_lattices(esk6_0,esk7_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_27])])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_48,plain,(
    ! [X15,X16,X17] :
      ( ( ~ v9_lattices(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | k2_lattices(X15,X16,k1_lattices(X15,X16,X17)) = X16
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( m1_subset_1(esk4_1(X15),u1_struct_0(X15))
        | v9_lattices(X15)
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( m1_subset_1(esk5_1(X15),u1_struct_0(X15))
        | v9_lattices(X15)
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) )
      & ( k2_lattices(X15,esk4_1(X15),k1_lattices(X15,esk4_1(X15),esk5_1(X15))) != esk4_1(X15)
        | v9_lattices(X15)
        | v2_struct_0(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).

fof(c_0_49,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v8_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | k1_lattices(X10,k2_lattices(X10,X11,X12),X12) = X12
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( m1_subset_1(esk2_1(X10),u1_struct_0(X10))
        | v8_lattices(X10)
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( m1_subset_1(esk3_1(X10),u1_struct_0(X10))
        | v8_lattices(X10)
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( k1_lattices(X10,k2_lattices(X10,esk2_1(X10),esk3_1(X10)),esk3_1(X10)) != esk3_1(X10)
        | v8_lattices(X10)
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).

fof(c_0_50,plain,(
    ! [X23] :
      ( v2_struct_0(X23)
      | ~ l2_lattices(X23)
      | m1_subset_1(k6_lattices(X23),u1_struct_0(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_lattices])])])).

cnf(c_0_51,negated_conjecture,
    ( X1 = esk7_0
    | ~ r1_lattices(esk6_0,esk7_0,X1)
    | ~ r1_lattices(esk6_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_27]),c_0_41])]),c_0_21])).

cnf(c_0_52,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( r1_lattices(esk6_0,k2_lattices(esk6_0,X1,esk7_0),k2_lattices(esk6_0,X2,esk7_0))
    | ~ r1_lattices(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_27]),c_0_28]),c_0_29]),c_0_44]),c_0_20])]),c_0_21])).

cnf(c_0_54,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_27])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk6_0,X1,esk7_0),u1_struct_0(esk6_0))
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_27]),c_0_21])).

cnf(c_0_56,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,plain,
    ( k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_60,plain,(
    ! [X25,X26,X27] :
      ( v2_struct_0(X25)
      | ~ v6_lattices(X25)
      | ~ l1_lattices(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ m1_subset_1(X27,u1_struct_0(X25))
      | k4_lattices(X25,X26,X27) = k2_lattices(X25,X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

cnf(c_0_61,negated_conjecture,
    ( X1 = esk7_0
    | ~ r1_lattices(esk6_0,esk7_0,X1)
    | ~ r1_lattices(esk6_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_20])])).

cnf(c_0_62,negated_conjecture,
    ( r1_lattices(esk6_0,esk7_0,k2_lattices(esk6_0,X1,esk7_0))
    | ~ r1_lattices(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_27])])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk6_0,X1,esk7_0),u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_20])])).

cnf(c_0_64,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X3) != X2
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_65,negated_conjecture,
    ( k2_lattices(esk6_0,X1,k1_lattices(esk6_0,X1,esk7_0)) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_27]),c_0_28]),c_0_20])]),c_0_21])).

cnf(c_0_66,negated_conjecture,
    ( k1_lattices(esk6_0,k2_lattices(esk6_0,X1,esk7_0),esk7_0) = esk7_0
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_27]),c_0_29]),c_0_20])]),c_0_21])).

cnf(c_0_67,plain,
    ( m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_52])).

fof(c_0_68,plain,(
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

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( k2_lattices(esk6_0,X1,esk7_0) = esk7_0
    | ~ r1_lattices(esk6_0,k2_lattices(esk6_0,X1,esk7_0),esk7_0)
    | ~ r1_lattices(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( r1_lattices(esk6_0,X1,esk7_0)
    | k2_lattices(esk6_0,X1,esk7_0) != X1
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_27]),c_0_28]),c_0_29]),c_0_20])]),c_0_21])).

cnf(c_0_72,negated_conjecture,
    ( k2_lattices(esk6_0,k2_lattices(esk6_0,X1,esk7_0),esk7_0) = k2_lattices(esk6_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(k6_lattices(esk6_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_20]),c_0_21])).

cnf(c_0_74,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k6_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v14_lattices(X1)
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( k4_lattices(esk6_0,k6_lattices(esk6_0),esk7_0) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_76,negated_conjecture,
    ( k4_lattices(esk6_0,X1,esk7_0) = k2_lattices(esk6_0,X1,esk7_0)
    | ~ l1_lattices(esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_27]),c_0_30])]),c_0_21])).

cnf(c_0_77,negated_conjecture,
    ( k2_lattices(esk6_0,X1,esk7_0) = esk7_0
    | ~ r1_lattices(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_63]),c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( r1_lattices(esk6_0,X1,k6_lattices(esk6_0))
    | k2_lattices(esk6_0,X1,k6_lattices(esk6_0)) != X1
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_73]),c_0_28]),c_0_29]),c_0_20])]),c_0_21])).

cnf(c_0_79,plain,
    ( k1_lattices(X1,X2,k6_lattices(X1)) = k6_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v14_lattices(X1)
    | ~ l2_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]),c_0_59])).

cnf(c_0_80,negated_conjecture,
    ( v14_lattices(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_81,negated_conjecture,
    ( k2_lattices(esk6_0,k6_lattices(esk6_0),esk7_0) != esk7_0
    | ~ l1_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_73])])).

cnf(c_0_82,negated_conjecture,
    ( k2_lattices(esk6_0,k6_lattices(esk6_0),esk7_0) = esk7_0
    | k2_lattices(esk6_0,esk7_0,k6_lattices(esk6_0)) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_73]),c_0_27])])).

cnf(c_0_83,negated_conjecture,
    ( k2_lattices(esk6_0,X1,k1_lattices(esk6_0,X1,k6_lattices(esk6_0))) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_73]),c_0_28]),c_0_20])]),c_0_21])).

cnf(c_0_84,negated_conjecture,
    ( k1_lattices(esk6_0,esk7_0,k6_lattices(esk6_0)) = k6_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_27]),c_0_80])]),c_0_21])).

cnf(c_0_85,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k6_lattices(esk6_0)) != esk7_0
    | ~ l1_lattices(esk6_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( k2_lattices(esk6_0,esk7_0,k6_lattices(esk6_0)) = esk7_0
    | ~ l2_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_27])])).

cnf(c_0_87,negated_conjecture,
    ( ~ l1_lattices(esk6_0)
    | ~ l2_lattices(esk6_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_88,negated_conjecture,
    ( ~ l2_lattices(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_56]),c_0_20])])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_52]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.030 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t43_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v14_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,k6_lattices(X1),X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_lattices)).
% 0.20/0.42  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.20/0.42  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.20/0.42  fof(reflexivity_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_lattices(X1,X2,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_lattices)).
% 0.20/0.42  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 0.20/0.42  fof(t26_lattices, axiom, ![X1]:(((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_lattices(X1,X2,X3)&r1_lattices(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_lattices)).
% 0.20/0.42  fof(t27_lattices, axiom, ![X1]:(((((~(v2_struct_0(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)=>r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_lattices)).
% 0.20/0.42  fof(dt_k2_lattices, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_lattices)).
% 0.20/0.42  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.20/0.42  fof(d9_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v9_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattices)).
% 0.20/0.42  fof(d8_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v8_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattices)).
% 0.20/0.42  fof(dt_k6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>m1_subset_1(k6_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_lattices)).
% 0.20/0.42  fof(redefinition_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 0.20/0.42  fof(d17_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>(v14_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k6_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k1_lattices(X1,X2,X3)=X2&k1_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattices)).
% 0.20/0.42  fof(c_0_14, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v14_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,k6_lattices(X1),X2)=X2))), inference(assume_negation,[status(cth)],[t43_lattices])).
% 0.20/0.42  fof(c_0_15, plain, ![X5]:(((((((~v2_struct_0(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))&(v4_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v5_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v6_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v7_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v8_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5)))&(v9_lattices(X5)|(v2_struct_0(X5)|~v10_lattices(X5))|~l3_lattices(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.20/0.42  fof(c_0_16, negated_conjecture, ((((~v2_struct_0(esk6_0)&v10_lattices(esk6_0))&v14_lattices(esk6_0))&l3_lattices(esk6_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&k4_lattices(esk6_0,k6_lattices(esk6_0),esk7_0)!=esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.20/0.42  fof(c_0_17, plain, ![X28, X29, X30]:((~r3_lattices(X28,X29,X30)|r1_lattices(X28,X29,X30)|(v2_struct_0(X28)|~v6_lattices(X28)|~v8_lattices(X28)|~v9_lattices(X28)|~l3_lattices(X28)|~m1_subset_1(X29,u1_struct_0(X28))|~m1_subset_1(X30,u1_struct_0(X28))))&(~r1_lattices(X28,X29,X30)|r3_lattices(X28,X29,X30)|(v2_struct_0(X28)|~v6_lattices(X28)|~v8_lattices(X28)|~v9_lattices(X28)|~l3_lattices(X28)|~m1_subset_1(X29,u1_struct_0(X28))|~m1_subset_1(X30,u1_struct_0(X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.20/0.42  cnf(c_0_18, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_19, negated_conjecture, (v10_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_20, negated_conjecture, (l3_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_22, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_23, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  fof(c_0_24, plain, ![X31, X32, X33]:(v2_struct_0(X31)|~v6_lattices(X31)|~v8_lattices(X31)|~v9_lattices(X31)|~l3_lattices(X31)|~m1_subset_1(X32,u1_struct_0(X31))|~m1_subset_1(X33,u1_struct_0(X31))|r3_lattices(X31,X32,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_lattices])])])).
% 0.20/0.42  fof(c_0_25, plain, ![X34, X35, X36]:((~r1_lattices(X34,X35,X36)|k2_lattices(X34,X35,X36)=X35|~m1_subset_1(X36,u1_struct_0(X34))|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v8_lattices(X34)|~v9_lattices(X34)|~l3_lattices(X34)))&(k2_lattices(X34,X35,X36)!=X35|r1_lattices(X34,X35,X36)|~m1_subset_1(X36,u1_struct_0(X34))|~m1_subset_1(X35,u1_struct_0(X34))|(v2_struct_0(X34)|~v8_lattices(X34)|~v9_lattices(X34)|~l3_lattices(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.20/0.42  cnf(c_0_26, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.42  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_28, negated_conjecture, (v9_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.42  cnf(c_0_29, negated_conjecture, (v8_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.42  cnf(c_0_30, negated_conjecture, (v6_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.42  cnf(c_0_31, plain, (v2_struct_0(X1)|r3_lattices(X1,X2,X2)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  fof(c_0_32, plain, ![X37, X38, X39]:(v2_struct_0(X37)|~v4_lattices(X37)|~l2_lattices(X37)|(~m1_subset_1(X38,u1_struct_0(X37))|(~m1_subset_1(X39,u1_struct_0(X37))|(~r1_lattices(X37,X38,X39)|~r1_lattices(X37,X39,X38)|X38=X39)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).
% 0.20/0.42  cnf(c_0_33, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  fof(c_0_34, plain, ![X40, X41, X42, X43]:(v2_struct_0(X40)|~v7_lattices(X40)|~v8_lattices(X40)|~v9_lattices(X40)|~l3_lattices(X40)|(~m1_subset_1(X41,u1_struct_0(X40))|(~m1_subset_1(X42,u1_struct_0(X40))|(~m1_subset_1(X43,u1_struct_0(X40))|(~r1_lattices(X40,X41,X42)|r1_lattices(X40,k2_lattices(X40,X41,X43),k2_lattices(X40,X42,X43))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_lattices])])])])).
% 0.20/0.42  cnf(c_0_35, plain, (v7_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_36, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.42  cnf(c_0_37, negated_conjecture, (r1_lattices(esk6_0,X1,esk7_0)|~r3_lattices(esk6_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_20])]), c_0_21])).
% 0.20/0.42  cnf(c_0_38, negated_conjecture, (r3_lattices(esk6_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_20])]), c_0_21])).
% 0.20/0.42  fof(c_0_39, plain, ![X20, X21, X22]:(v2_struct_0(X20)|~l1_lattices(X20)|~m1_subset_1(X21,u1_struct_0(X20))|~m1_subset_1(X22,u1_struct_0(X20))|m1_subset_1(k2_lattices(X20,X21,X22),u1_struct_0(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_lattices])])])).
% 0.20/0.42  cnf(c_0_40, plain, (v2_struct_0(X1)|X2=X3|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattices(X1,X2,X3)|~r1_lattices(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  cnf(c_0_41, negated_conjecture, (v4_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.42  fof(c_0_42, plain, ![X24]:((l1_lattices(X24)|~l3_lattices(X24))&(l2_lattices(X24)|~l3_lattices(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.20/0.42  cnf(c_0_43, plain, (v2_struct_0(X1)|r1_lattices(X1,k2_lattices(X1,X2,X4),k2_lattices(X1,X3,X4))|~v7_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~r1_lattices(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.42  cnf(c_0_44, negated_conjecture, (v7_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.42  cnf(c_0_45, negated_conjecture, (k2_lattices(esk6_0,X1,esk7_0)=X1|~r1_lattices(esk6_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_27]), c_0_28]), c_0_29]), c_0_20])]), c_0_21])).
% 0.20/0.42  cnf(c_0_46, negated_conjecture, (r1_lattices(esk6_0,esk7_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_27])])).
% 0.20/0.42  cnf(c_0_47, plain, (v2_struct_0(X1)|m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.42  fof(c_0_48, plain, ![X15, X16, X17]:((~v9_lattices(X15)|(~m1_subset_1(X16,u1_struct_0(X15))|(~m1_subset_1(X17,u1_struct_0(X15))|k2_lattices(X15,X16,k1_lattices(X15,X16,X17))=X16))|(v2_struct_0(X15)|~l3_lattices(X15)))&((m1_subset_1(esk4_1(X15),u1_struct_0(X15))|v9_lattices(X15)|(v2_struct_0(X15)|~l3_lattices(X15)))&((m1_subset_1(esk5_1(X15),u1_struct_0(X15))|v9_lattices(X15)|(v2_struct_0(X15)|~l3_lattices(X15)))&(k2_lattices(X15,esk4_1(X15),k1_lattices(X15,esk4_1(X15),esk5_1(X15)))!=esk4_1(X15)|v9_lattices(X15)|(v2_struct_0(X15)|~l3_lattices(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).
% 0.20/0.42  fof(c_0_49, plain, ![X10, X11, X12]:((~v8_lattices(X10)|(~m1_subset_1(X11,u1_struct_0(X10))|(~m1_subset_1(X12,u1_struct_0(X10))|k1_lattices(X10,k2_lattices(X10,X11,X12),X12)=X12))|(v2_struct_0(X10)|~l3_lattices(X10)))&((m1_subset_1(esk2_1(X10),u1_struct_0(X10))|v8_lattices(X10)|(v2_struct_0(X10)|~l3_lattices(X10)))&((m1_subset_1(esk3_1(X10),u1_struct_0(X10))|v8_lattices(X10)|(v2_struct_0(X10)|~l3_lattices(X10)))&(k1_lattices(X10,k2_lattices(X10,esk2_1(X10),esk3_1(X10)),esk3_1(X10))!=esk3_1(X10)|v8_lattices(X10)|(v2_struct_0(X10)|~l3_lattices(X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).
% 0.20/0.42  fof(c_0_50, plain, ![X23]:(v2_struct_0(X23)|~l2_lattices(X23)|m1_subset_1(k6_lattices(X23),u1_struct_0(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_lattices])])])).
% 0.20/0.42  cnf(c_0_51, negated_conjecture, (X1=esk7_0|~r1_lattices(esk6_0,esk7_0,X1)|~r1_lattices(esk6_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~l2_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_27]), c_0_41])]), c_0_21])).
% 0.20/0.42  cnf(c_0_52, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.42  cnf(c_0_53, negated_conjecture, (r1_lattices(esk6_0,k2_lattices(esk6_0,X1,esk7_0),k2_lattices(esk6_0,X2,esk7_0))|~r1_lattices(esk6_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_27]), c_0_28]), c_0_29]), c_0_44]), c_0_20])]), c_0_21])).
% 0.20/0.42  cnf(c_0_54, negated_conjecture, (k2_lattices(esk6_0,esk7_0,esk7_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_27])])).
% 0.20/0.42  cnf(c_0_55, negated_conjecture, (m1_subset_1(k2_lattices(esk6_0,X1,esk7_0),u1_struct_0(esk6_0))|~l1_lattices(esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_27]), c_0_21])).
% 0.20/0.42  cnf(c_0_56, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.42  cnf(c_0_57, plain, (k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2|v2_struct_0(X1)|~v9_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.42  cnf(c_0_58, plain, (k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3|v2_struct_0(X1)|~v8_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.42  cnf(c_0_59, plain, (v2_struct_0(X1)|m1_subset_1(k6_lattices(X1),u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.42  fof(c_0_60, plain, ![X25, X26, X27]:(v2_struct_0(X25)|~v6_lattices(X25)|~l1_lattices(X25)|~m1_subset_1(X26,u1_struct_0(X25))|~m1_subset_1(X27,u1_struct_0(X25))|k4_lattices(X25,X26,X27)=k2_lattices(X25,X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).
% 0.20/0.42  cnf(c_0_61, negated_conjecture, (X1=esk7_0|~r1_lattices(esk6_0,esk7_0,X1)|~r1_lattices(esk6_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_20])])).
% 0.20/0.42  cnf(c_0_62, negated_conjecture, (r1_lattices(esk6_0,esk7_0,k2_lattices(esk6_0,X1,esk7_0))|~r1_lattices(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_27])])).
% 0.20/0.42  cnf(c_0_63, negated_conjecture, (m1_subset_1(k2_lattices(esk6_0,X1,esk7_0),u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_20])])).
% 0.20/0.42  cnf(c_0_64, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k2_lattices(X1,X2,X3)!=X2|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.42  cnf(c_0_65, negated_conjecture, (k2_lattices(esk6_0,X1,k1_lattices(esk6_0,X1,esk7_0))=X1|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_27]), c_0_28]), c_0_20])]), c_0_21])).
% 0.20/0.42  cnf(c_0_66, negated_conjecture, (k1_lattices(esk6_0,k2_lattices(esk6_0,X1,esk7_0),esk7_0)=esk7_0|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_27]), c_0_29]), c_0_20])]), c_0_21])).
% 0.20/0.42  cnf(c_0_67, plain, (m1_subset_1(k6_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_59, c_0_52])).
% 0.20/0.42  fof(c_0_68, plain, ![X6, X7, X8]:(((k1_lattices(X6,X7,X8)=X7|~m1_subset_1(X8,u1_struct_0(X6))|X7!=k6_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~v14_lattices(X6)|(v2_struct_0(X6)|~l2_lattices(X6)))&(k1_lattices(X6,X8,X7)=X7|~m1_subset_1(X8,u1_struct_0(X6))|X7!=k6_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~v14_lattices(X6)|(v2_struct_0(X6)|~l2_lattices(X6))))&((m1_subset_1(esk1_2(X6,X7),u1_struct_0(X6))|X7=k6_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~v14_lattices(X6)|(v2_struct_0(X6)|~l2_lattices(X6)))&(k1_lattices(X6,X7,esk1_2(X6,X7))!=X7|k1_lattices(X6,esk1_2(X6,X7),X7)!=X7|X7=k6_lattices(X6)|~m1_subset_1(X7,u1_struct_0(X6))|~v14_lattices(X6)|(v2_struct_0(X6)|~l2_lattices(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattices])])])])])])).
% 0.20/0.42  cnf(c_0_69, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.42  cnf(c_0_70, negated_conjecture, (k2_lattices(esk6_0,X1,esk7_0)=esk7_0|~r1_lattices(esk6_0,k2_lattices(esk6_0,X1,esk7_0),esk7_0)|~r1_lattices(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 0.20/0.42  cnf(c_0_71, negated_conjecture, (r1_lattices(esk6_0,X1,esk7_0)|k2_lattices(esk6_0,X1,esk7_0)!=X1|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_27]), c_0_28]), c_0_29]), c_0_20])]), c_0_21])).
% 0.20/0.42  cnf(c_0_72, negated_conjecture, (k2_lattices(esk6_0,k2_lattices(esk6_0,X1,esk7_0),esk7_0)=k2_lattices(esk6_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_63])).
% 0.20/0.42  cnf(c_0_73, negated_conjecture, (m1_subset_1(k6_lattices(esk6_0),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_20]), c_0_21])).
% 0.20/0.42  cnf(c_0_74, plain, (k1_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k6_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v14_lattices(X1)|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.42  cnf(c_0_75, negated_conjecture, (k4_lattices(esk6_0,k6_lattices(esk6_0),esk7_0)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_76, negated_conjecture, (k4_lattices(esk6_0,X1,esk7_0)=k2_lattices(esk6_0,X1,esk7_0)|~l1_lattices(esk6_0)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_27]), c_0_30])]), c_0_21])).
% 0.20/0.42  cnf(c_0_77, negated_conjecture, (k2_lattices(esk6_0,X1,esk7_0)=esk7_0|~r1_lattices(esk6_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_63]), c_0_72])).
% 0.20/0.42  cnf(c_0_78, negated_conjecture, (r1_lattices(esk6_0,X1,k6_lattices(esk6_0))|k2_lattices(esk6_0,X1,k6_lattices(esk6_0))!=X1|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_73]), c_0_28]), c_0_29]), c_0_20])]), c_0_21])).
% 0.20/0.42  cnf(c_0_79, plain, (k1_lattices(X1,X2,k6_lattices(X1))=k6_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v14_lattices(X1)|~l2_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]), c_0_59])).
% 0.20/0.42  cnf(c_0_80, negated_conjecture, (v14_lattices(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_81, negated_conjecture, (k2_lattices(esk6_0,k6_lattices(esk6_0),esk7_0)!=esk7_0|~l1_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_73])])).
% 0.20/0.42  cnf(c_0_82, negated_conjecture, (k2_lattices(esk6_0,k6_lattices(esk6_0),esk7_0)=esk7_0|k2_lattices(esk6_0,esk7_0,k6_lattices(esk6_0))!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_73]), c_0_27])])).
% 0.20/0.42  cnf(c_0_83, negated_conjecture, (k2_lattices(esk6_0,X1,k1_lattices(esk6_0,X1,k6_lattices(esk6_0)))=X1|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_73]), c_0_28]), c_0_20])]), c_0_21])).
% 0.20/0.42  cnf(c_0_84, negated_conjecture, (k1_lattices(esk6_0,esk7_0,k6_lattices(esk6_0))=k6_lattices(esk6_0)|~l2_lattices(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_27]), c_0_80])]), c_0_21])).
% 0.20/0.42  cnf(c_0_85, negated_conjecture, (k2_lattices(esk6_0,esk7_0,k6_lattices(esk6_0))!=esk7_0|~l1_lattices(esk6_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.20/0.42  cnf(c_0_86, negated_conjecture, (k2_lattices(esk6_0,esk7_0,k6_lattices(esk6_0))=esk7_0|~l2_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_27])])).
% 0.20/0.42  cnf(c_0_87, negated_conjecture, (~l1_lattices(esk6_0)|~l2_lattices(esk6_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.20/0.42  cnf(c_0_88, negated_conjecture, (~l2_lattices(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_56]), c_0_20])])).
% 0.20/0.42  cnf(c_0_89, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_52]), c_0_20])]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 90
% 0.20/0.42  # Proof object clause steps            : 61
% 0.20/0.42  # Proof object formula steps           : 29
% 0.20/0.42  # Proof object conjectures             : 43
% 0.20/0.42  # Proof object clause conjectures      : 40
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 25
% 0.20/0.42  # Proof object initial formulas used   : 14
% 0.20/0.42  # Proof object generating inferences   : 35
% 0.20/0.42  # Proof object simplifying inferences  : 98
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 14
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 37
% 0.20/0.42  # Removed in clause preprocessing      : 1
% 0.20/0.42  # Initial clauses in saturation        : 36
% 0.20/0.42  # Processed clauses                    : 376
% 0.20/0.42  # ...of these trivial                  : 0
% 0.20/0.42  # ...subsumed                          : 87
% 0.20/0.42  # ...remaining for further processing  : 289
% 0.20/0.42  # Other redundant clauses eliminated   : 2
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 43
% 0.20/0.42  # Backward-rewritten                   : 0
% 0.20/0.42  # Generated clauses                    : 1094
% 0.20/0.42  # ...of the previous two non-trivial   : 1043
% 0.20/0.42  # Contextual simplify-reflections      : 15
% 0.20/0.42  # Paramodulations                      : 1092
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 2
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 208
% 0.20/0.42  #    Positive orientable unit clauses  : 17
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 3
% 0.20/0.42  #    Non-unit-clauses                  : 188
% 0.20/0.42  # Current number of unprocessed clauses: 739
% 0.20/0.42  # ...number of literals in the above   : 2511
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 79
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 9945
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 4617
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 144
% 0.20/0.42  # Unit Clause-clause subsumption calls : 162
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 13
% 0.20/0.42  # BW rewrite match successes           : 1
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 39188
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.076 s
% 0.20/0.42  # System time              : 0.002 s
% 0.20/0.42  # Total time               : 0.078 s
% 0.20/0.42  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
