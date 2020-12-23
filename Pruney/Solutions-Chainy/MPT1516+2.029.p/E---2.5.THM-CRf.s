%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:10 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 535 expanded)
%              Number of clauses        :   41 ( 186 expanded)
%              Number of leaves         :   13 ( 134 expanded)
%              Depth                    :   19
%              Number of atoms          :  447 (3892 expanded)
%              Number of equality atoms :   48 ( 409 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal clause size      :   28 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1)
        & k5_lattices(X1) = k15_lattice3(X1,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).

fof(t48_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2,X3] :
          ( ! [X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ~ ( r2_hidden(X4,X2)
                  & ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X1))
                     => ~ ( r3_lattices(X1,X4,X5)
                          & r2_hidden(X5,X3) ) ) ) )
         => r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattice3)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(t45_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( X2 = k15_lattice3(X1,a_2_3_lattice3(X1,X2))
            & X2 = k16_lattice3(X1,a_2_4_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).

fof(d13_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v13_lattices(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( k2_lattices(X1,X2,X3) = X2
                  & k2_lattices(X1,X3,X2) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).

fof(d6_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v6_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(d16_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v13_lattices(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( X2 = k5_lattices(X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( k2_lattices(X1,X2,X3) = X2
                    & k2_lattices(X1,X3,X2) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

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

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v13_lattices(X1)
          & l3_lattices(X1)
          & k5_lattices(X1) = k15_lattice3(X1,k1_xboole_0) ) ) ),
    inference(assume_negation,[status(cth)],[t50_lattice3])).

fof(c_0_14,plain,(
    ! [X35,X36,X37,X39] :
      ( ( m1_subset_1(esk6_3(X35,X36,X37),u1_struct_0(X35))
        | r3_lattices(X35,k15_lattice3(X35,X36),k15_lattice3(X35,X37))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) )
      & ( r2_hidden(esk6_3(X35,X36,X37),X36)
        | r3_lattices(X35,k15_lattice3(X35,X36),k15_lattice3(X35,X37))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) )
      & ( ~ m1_subset_1(X39,u1_struct_0(X35))
        | ~ r3_lattices(X35,esk6_3(X35,X36,X37),X39)
        | ~ r2_hidden(X39,X37)
        | r3_lattices(X35,k15_lattice3(X35,X36),k15_lattice3(X35,X37))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v10_lattices(esk7_0)
    & v4_lattice3(esk7_0)
    & l3_lattices(esk7_0)
    & ( v2_struct_0(esk7_0)
      | ~ v10_lattices(esk7_0)
      | ~ v13_lattices(esk7_0)
      | ~ l3_lattices(esk7_0)
      | k5_lattices(esk7_0) != k15_lattice3(esk7_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | ~ r1_tarski(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_17,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v4_lattice3(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v10_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( l3_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r3_lattices(esk7_0,k15_lattice3(esk7_0,X1),k15_lattice3(esk7_0,X2))
    | r2_hidden(esk6_3(esk7_0,X1,X2),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

fof(c_0_24,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_25,plain,(
    ! [X18,X19,X20] :
      ( ( ~ r1_lattices(X18,X19,X20)
        | k2_lattices(X18,X19,X20) = X19
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v8_lattices(X18)
        | ~ v9_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( k2_lattices(X18,X19,X20) != X19
        | r1_lattices(X18,X19,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ v8_lattices(X18)
        | ~ v9_lattices(X18)
        | ~ l3_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

fof(c_0_26,plain,(
    ! [X15,X16,X17] :
      ( ( ~ r3_lattices(X15,X16,X17)
        | r1_lattices(X15,X16,X17)
        | v2_struct_0(X15)
        | ~ v6_lattices(X15)
        | ~ v8_lattices(X15)
        | ~ v9_lattices(X15)
        | ~ l3_lattices(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15)) )
      & ( ~ r1_lattices(X15,X16,X17)
        | r3_lattices(X15,X16,X17)
        | v2_struct_0(X15)
        | ~ v6_lattices(X15)
        | ~ v8_lattices(X15)
        | ~ v9_lattices(X15)
        | ~ l3_lattices(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_27,negated_conjecture,
    ( r3_lattices(esk7_0,k15_lattice3(esk7_0,X1),k15_lattice3(esk7_0,X2))
    | ~ r1_tarski(X1,esk6_3(esk7_0,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X33,X34] :
      ( ( X34 = k15_lattice3(X33,a_2_3_lattice3(X33,X34))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ v4_lattice3(X33)
        | ~ l3_lattices(X33) )
      & ( X34 = k16_lattice3(X33,a_2_4_lattice3(X33,X34))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v10_lattices(X33)
        | ~ v4_lattice3(X33)
        | ~ l3_lattices(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).

fof(c_0_30,plain,(
    ! [X21,X23,X24] :
      ( ( m1_subset_1(esk2_1(X21),u1_struct_0(X21))
        | ~ v13_lattices(X21)
        | v2_struct_0(X21)
        | ~ l1_lattices(X21) )
      & ( k2_lattices(X21,esk2_1(X21),X23) = esk2_1(X21)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ v13_lattices(X21)
        | v2_struct_0(X21)
        | ~ l1_lattices(X21) )
      & ( k2_lattices(X21,X23,esk2_1(X21)) = esk2_1(X21)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ v13_lattices(X21)
        | v2_struct_0(X21)
        | ~ l1_lattices(X21) )
      & ( m1_subset_1(esk3_2(X21,X24),u1_struct_0(X21))
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | v13_lattices(X21)
        | v2_struct_0(X21)
        | ~ l1_lattices(X21) )
      & ( k2_lattices(X21,X24,esk3_2(X21,X24)) != X24
        | k2_lattices(X21,esk3_2(X21,X24),X24) != X24
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | v13_lattices(X21)
        | v2_struct_0(X21)
        | ~ l1_lattices(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

fof(c_0_31,plain,(
    ! [X26,X27,X28] :
      ( ( ~ v6_lattices(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | k2_lattices(X26,X27,X28) = k2_lattices(X26,X28,X27)
        | v2_struct_0(X26)
        | ~ l1_lattices(X26) )
      & ( m1_subset_1(esk4_1(X26),u1_struct_0(X26))
        | v6_lattices(X26)
        | v2_struct_0(X26)
        | ~ l1_lattices(X26) )
      & ( m1_subset_1(esk5_1(X26),u1_struct_0(X26))
        | v6_lattices(X26)
        | v2_struct_0(X26)
        | ~ l1_lattices(X26) )
      & ( k2_lattices(X26,esk4_1(X26),esk5_1(X26)) != k2_lattices(X26,esk5_1(X26),esk4_1(X26))
        | v6_lattices(X26)
        | v2_struct_0(X26)
        | ~ l1_lattices(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

cnf(c_0_32,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( r3_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k15_lattice3(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( X1 = k15_lattice3(X2,a_2_3_lattice3(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | k2_lattices(X1,esk3_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r3_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_41,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),X1) = k15_lattice3(esk7_0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(esk7_0,k1_xboole_0),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_20])]),c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( v13_lattices(esk7_0)
    | ~ m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0)),u1_struct_0(esk7_0))
    | ~ m1_subset_1(k15_lattice3(esk7_0,k1_xboole_0),u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0)
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_21])).

fof(c_0_44,plain,(
    ! [X31,X32] :
      ( v2_struct_0(X31)
      | ~ l3_lattices(X31)
      | m1_subset_1(k15_lattice3(X31,X32),u1_struct_0(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_45,plain,(
    ! [X10,X11,X12] :
      ( ( k2_lattices(X10,X11,X12) = X11
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | X11 != k5_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v13_lattices(X10)
        | v2_struct_0(X10)
        | ~ l1_lattices(X10) )
      & ( k2_lattices(X10,X12,X11) = X11
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | X11 != k5_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v13_lattices(X10)
        | v2_struct_0(X10)
        | ~ l1_lattices(X10) )
      & ( m1_subset_1(esk1_2(X10,X11),u1_struct_0(X10))
        | X11 = k5_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v13_lattices(X10)
        | v2_struct_0(X10)
        | ~ l1_lattices(X10) )
      & ( k2_lattices(X10,X11,esk1_2(X10,X11)) != X11
        | k2_lattices(X10,esk1_2(X10,X11),X11) != X11
        | X11 = k5_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ v13_lattices(X10)
        | v2_struct_0(X10)
        | ~ l1_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

cnf(c_0_46,negated_conjecture,
    ( v13_lattices(esk7_0)
    | ~ m1_subset_1(k15_lattice3(esk7_0,k1_xboole_0),u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0)
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_38]),c_0_21])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,plain,
    ( X2 = k5_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk1_2(X1,X2)) != X2
    | k2_lattices(X1,esk1_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( k2_lattices(esk7_0,X1,k15_lattice3(esk7_0,k1_xboole_0)) = k15_lattice3(esk7_0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(esk7_0,k1_xboole_0),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0)
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_42]),c_0_21])).

cnf(c_0_50,negated_conjecture,
    ( v13_lattices(esk7_0)
    | ~ l1_lattices(esk7_0)
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_20])]),c_0_21])).

cnf(c_0_51,negated_conjecture,
    ( k15_lattice3(esk7_0,k1_xboole_0) = k5_lattices(esk7_0)
    | ~ m1_subset_1(esk1_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0)),u1_struct_0(esk7_0))
    | ~ m1_subset_1(k15_lattice3(esk7_0,k1_xboole_0),u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0)
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_21]),c_0_50]),c_0_42])).

cnf(c_0_52,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | X2 = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( v2_struct_0(esk7_0)
    | ~ v10_lattices(esk7_0)
    | ~ v13_lattices(esk7_0)
    | ~ l3_lattices(esk7_0)
    | k5_lattices(esk7_0) != k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( k15_lattice3(esk7_0,k1_xboole_0) = k5_lattices(esk7_0)
    | ~ m1_subset_1(k15_lattice3(esk7_0,k1_xboole_0),u1_struct_0(esk7_0))
    | ~ l1_lattices(esk7_0)
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_21]),c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( k15_lattice3(esk7_0,k1_xboole_0) != k5_lattices(esk7_0)
    | ~ v13_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_20]),c_0_19])]),c_0_21])).

cnf(c_0_56,negated_conjecture,
    ( k15_lattice3(esk7_0,k1_xboole_0) = k5_lattices(esk7_0)
    | ~ l1_lattices(esk7_0)
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_47]),c_0_20])]),c_0_21])).

fof(c_0_57,plain,(
    ! [X9] :
      ( ( ~ v2_struct_0(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v4_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v5_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v6_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v7_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v8_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) )
      & ( v9_lattices(X9)
        | v2_struct_0(X9)
        | ~ v10_lattices(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_58,negated_conjecture,
    ( ~ l1_lattices(esk7_0)
    | ~ v9_lattices(esk7_0)
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_50])).

cnf(c_0_59,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( ~ l1_lattices(esk7_0)
    | ~ v8_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_61,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( ~ l1_lattices(esk7_0)
    | ~ v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_63,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_64,plain,(
    ! [X14] :
      ( ( l1_lattices(X14)
        | ~ l3_lattices(X14) )
      & ( l2_lattices(X14)
        | ~ l3_lattices(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_65,negated_conjecture,
    ( ~ l1_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_66,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:44:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.030 s
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_lattice3)).
% 0.14/0.38  fof(t48_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_lattice3)).
% 0.14/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.14/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.38  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 0.14/0.38  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.14/0.38  fof(t45_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k15_lattice3(X1,a_2_3_lattice3(X1,X2))&X2=k16_lattice3(X1,a_2_4_lattice3(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_lattice3)).
% 0.14/0.38  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_lattices)).
% 0.14/0.38  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_lattices)).
% 0.14/0.38  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.14/0.38  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 0.14/0.38  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.14/0.38  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.14/0.38  fof(c_0_13, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 0.14/0.38  fof(c_0_14, plain, ![X35, X36, X37, X39]:((m1_subset_1(esk6_3(X35,X36,X37),u1_struct_0(X35))|r3_lattices(X35,k15_lattice3(X35,X36),k15_lattice3(X35,X37))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)))&((r2_hidden(esk6_3(X35,X36,X37),X36)|r3_lattices(X35,k15_lattice3(X35,X36),k15_lattice3(X35,X37))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)))&(~m1_subset_1(X39,u1_struct_0(X35))|(~r3_lattices(X35,esk6_3(X35,X36,X37),X39)|~r2_hidden(X39,X37))|r3_lattices(X35,k15_lattice3(X35,X36),k15_lattice3(X35,X37))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).
% 0.14/0.38  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk7_0)&v10_lattices(esk7_0))&v4_lattice3(esk7_0))&l3_lattices(esk7_0))&(v2_struct_0(esk7_0)|~v10_lattices(esk7_0)|~v13_lattices(esk7_0)|~l3_lattices(esk7_0)|k5_lattices(esk7_0)!=k15_lattice3(esk7_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.14/0.38  fof(c_0_16, plain, ![X7, X8]:(~r2_hidden(X7,X8)|~r1_tarski(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.14/0.38  cnf(c_0_17, plain, (r2_hidden(esk6_3(X1,X2,X3),X2)|r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (v4_lattice3(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (v10_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (l3_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (r3_lattices(esk7_0,k15_lattice3(esk7_0,X1),k15_lattice3(esk7_0,X2))|r2_hidden(esk6_3(esk7_0,X1,X2),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.14/0.38  fof(c_0_24, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.38  fof(c_0_25, plain, ![X18, X19, X20]:((~r1_lattices(X18,X19,X20)|k2_lattices(X18,X19,X20)=X19|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v8_lattices(X18)|~v9_lattices(X18)|~l3_lattices(X18)))&(k2_lattices(X18,X19,X20)!=X19|r1_lattices(X18,X19,X20)|~m1_subset_1(X20,u1_struct_0(X18))|~m1_subset_1(X19,u1_struct_0(X18))|(v2_struct_0(X18)|~v8_lattices(X18)|~v9_lattices(X18)|~l3_lattices(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.14/0.38  fof(c_0_26, plain, ![X15, X16, X17]:((~r3_lattices(X15,X16,X17)|r1_lattices(X15,X16,X17)|(v2_struct_0(X15)|~v6_lattices(X15)|~v8_lattices(X15)|~v9_lattices(X15)|~l3_lattices(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))))&(~r1_lattices(X15,X16,X17)|r3_lattices(X15,X16,X17)|(v2_struct_0(X15)|~v6_lattices(X15)|~v8_lattices(X15)|~v9_lattices(X15)|~l3_lattices(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (r3_lattices(esk7_0,k15_lattice3(esk7_0,X1),k15_lattice3(esk7_0,X2))|~r1_tarski(X1,esk6_3(esk7_0,X1,X2))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.38  cnf(c_0_28, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  fof(c_0_29, plain, ![X33, X34]:((X34=k15_lattice3(X33,a_2_3_lattice3(X33,X34))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v10_lattices(X33)|~v4_lattice3(X33)|~l3_lattices(X33)))&(X34=k16_lattice3(X33,a_2_4_lattice3(X33,X34))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v10_lattices(X33)|~v4_lattice3(X33)|~l3_lattices(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).
% 0.14/0.38  fof(c_0_30, plain, ![X21, X23, X24]:(((m1_subset_1(esk2_1(X21),u1_struct_0(X21))|~v13_lattices(X21)|(v2_struct_0(X21)|~l1_lattices(X21)))&((k2_lattices(X21,esk2_1(X21),X23)=esk2_1(X21)|~m1_subset_1(X23,u1_struct_0(X21))|~v13_lattices(X21)|(v2_struct_0(X21)|~l1_lattices(X21)))&(k2_lattices(X21,X23,esk2_1(X21))=esk2_1(X21)|~m1_subset_1(X23,u1_struct_0(X21))|~v13_lattices(X21)|(v2_struct_0(X21)|~l1_lattices(X21)))))&((m1_subset_1(esk3_2(X21,X24),u1_struct_0(X21))|~m1_subset_1(X24,u1_struct_0(X21))|v13_lattices(X21)|(v2_struct_0(X21)|~l1_lattices(X21)))&(k2_lattices(X21,X24,esk3_2(X21,X24))!=X24|k2_lattices(X21,esk3_2(X21,X24),X24)!=X24|~m1_subset_1(X24,u1_struct_0(X21))|v13_lattices(X21)|(v2_struct_0(X21)|~l1_lattices(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 0.14/0.38  fof(c_0_31, plain, ![X26, X27, X28]:((~v6_lattices(X26)|(~m1_subset_1(X27,u1_struct_0(X26))|(~m1_subset_1(X28,u1_struct_0(X26))|k2_lattices(X26,X27,X28)=k2_lattices(X26,X28,X27)))|(v2_struct_0(X26)|~l1_lattices(X26)))&((m1_subset_1(esk4_1(X26),u1_struct_0(X26))|v6_lattices(X26)|(v2_struct_0(X26)|~l1_lattices(X26)))&((m1_subset_1(esk5_1(X26),u1_struct_0(X26))|v6_lattices(X26)|(v2_struct_0(X26)|~l1_lattices(X26)))&(k2_lattices(X26,esk4_1(X26),esk5_1(X26))!=k2_lattices(X26,esk5_1(X26),esk4_1(X26))|v6_lattices(X26)|(v2_struct_0(X26)|~l1_lattices(X26)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 0.14/0.38  cnf(c_0_32, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.38  cnf(c_0_33, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (r3_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k15_lattice3(esk7_0,X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.14/0.38  cnf(c_0_35, plain, (X1=k15_lattice3(X2,a_2_3_lattice3(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.38  cnf(c_0_36, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|k2_lattices(X1,esk3_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_37, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.38  cnf(c_0_38, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_39, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v9_lattices(X1)|~v8_lattices(X1)|~v6_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (r3_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),X1)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.14/0.38  cnf(c_0_41, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)|~v6_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),X1)=k15_lattice3(esk7_0,k1_xboole_0)|~m1_subset_1(k15_lattice3(esk7_0,k1_xboole_0),u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~v9_lattices(esk7_0)|~v8_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_20])]), c_0_21])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (v13_lattices(esk7_0)|~m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0)),u1_struct_0(esk7_0))|~m1_subset_1(k15_lattice3(esk7_0,k1_xboole_0),u1_struct_0(esk7_0))|~l1_lattices(esk7_0)|~v9_lattices(esk7_0)|~v8_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_21])).
% 0.14/0.38  fof(c_0_44, plain, ![X31, X32]:(v2_struct_0(X31)|~l3_lattices(X31)|m1_subset_1(k15_lattice3(X31,X32),u1_struct_0(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.14/0.38  fof(c_0_45, plain, ![X10, X11, X12]:(((k2_lattices(X10,X11,X12)=X11|~m1_subset_1(X12,u1_struct_0(X10))|X11!=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10)))&(k2_lattices(X10,X12,X11)=X11|~m1_subset_1(X12,u1_struct_0(X10))|X11!=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10))))&((m1_subset_1(esk1_2(X10,X11),u1_struct_0(X10))|X11=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10)))&(k2_lattices(X10,X11,esk1_2(X10,X11))!=X11|k2_lattices(X10,esk1_2(X10,X11),X11)!=X11|X11=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (v13_lattices(esk7_0)|~m1_subset_1(k15_lattice3(esk7_0,k1_xboole_0),u1_struct_0(esk7_0))|~l1_lattices(esk7_0)|~v9_lattices(esk7_0)|~v8_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_38]), c_0_21])).
% 0.14/0.38  cnf(c_0_47, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.14/0.38  cnf(c_0_48, plain, (X2=k5_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk1_2(X1,X2))!=X2|k2_lattices(X1,esk1_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (k2_lattices(esk7_0,X1,k15_lattice3(esk7_0,k1_xboole_0))=k15_lattice3(esk7_0,k1_xboole_0)|~m1_subset_1(k15_lattice3(esk7_0,k1_xboole_0),u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))|~l1_lattices(esk7_0)|~v9_lattices(esk7_0)|~v8_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_42]), c_0_21])).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (v13_lattices(esk7_0)|~l1_lattices(esk7_0)|~v9_lattices(esk7_0)|~v8_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_20])]), c_0_21])).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (k15_lattice3(esk7_0,k1_xboole_0)=k5_lattices(esk7_0)|~m1_subset_1(esk1_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0)),u1_struct_0(esk7_0))|~m1_subset_1(k15_lattice3(esk7_0,k1_xboole_0),u1_struct_0(esk7_0))|~l1_lattices(esk7_0)|~v9_lattices(esk7_0)|~v8_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_21]), c_0_50]), c_0_42])).
% 0.14/0.38  cnf(c_0_52, plain, (m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|X2=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, (v2_struct_0(esk7_0)|~v10_lattices(esk7_0)|~v13_lattices(esk7_0)|~l3_lattices(esk7_0)|k5_lattices(esk7_0)!=k15_lattice3(esk7_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (k15_lattice3(esk7_0,k1_xboole_0)=k5_lattices(esk7_0)|~m1_subset_1(k15_lattice3(esk7_0,k1_xboole_0),u1_struct_0(esk7_0))|~l1_lattices(esk7_0)|~v9_lattices(esk7_0)|~v8_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_21]), c_0_50])).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (k15_lattice3(esk7_0,k1_xboole_0)!=k5_lattices(esk7_0)|~v13_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_20]), c_0_19])]), c_0_21])).
% 0.14/0.38  cnf(c_0_56, negated_conjecture, (k15_lattice3(esk7_0,k1_xboole_0)=k5_lattices(esk7_0)|~l1_lattices(esk7_0)|~v9_lattices(esk7_0)|~v8_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_47]), c_0_20])]), c_0_21])).
% 0.14/0.38  fof(c_0_57, plain, ![X9]:(((((((~v2_struct_0(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9))&(v4_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v5_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v6_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v7_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v8_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v9_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, (~l1_lattices(esk7_0)|~v9_lattices(esk7_0)|~v8_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_50])).
% 0.14/0.38  cnf(c_0_59, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.14/0.38  cnf(c_0_60, negated_conjecture, (~l1_lattices(esk7_0)|~v8_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_19]), c_0_20])]), c_0_21])).
% 0.14/0.38  cnf(c_0_61, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.14/0.38  cnf(c_0_62, negated_conjecture, (~l1_lattices(esk7_0)|~v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_19]), c_0_20])]), c_0_21])).
% 0.14/0.38  cnf(c_0_63, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.14/0.38  fof(c_0_64, plain, ![X14]:((l1_lattices(X14)|~l3_lattices(X14))&(l2_lattices(X14)|~l3_lattices(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.14/0.38  cnf(c_0_65, negated_conjecture, (~l1_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_19]), c_0_20])]), c_0_21])).
% 0.14/0.38  cnf(c_0_66, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.14/0.38  cnf(c_0_67, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_20])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 68
% 0.14/0.38  # Proof object clause steps            : 41
% 0.14/0.38  # Proof object formula steps           : 27
% 0.14/0.38  # Proof object conjectures             : 26
% 0.14/0.38  # Proof object clause conjectures      : 23
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 21
% 0.14/0.38  # Proof object initial formulas used   : 13
% 0.14/0.38  # Proof object generating inferences   : 19
% 0.14/0.38  # Proof object simplifying inferences  : 46
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 13
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 39
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 38
% 0.14/0.38  # Processed clauses                    : 99
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 14
% 0.14/0.38  # ...remaining for further processing  : 85
% 0.14/0.38  # Other redundant clauses eliminated   : 2
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 25
% 0.14/0.38  # Backward-rewritten                   : 0
% 0.14/0.38  # Generated clauses                    : 114
% 0.14/0.38  # ...of the previous two non-trivial   : 103
% 0.14/0.38  # Contextual simplify-reflections      : 11
% 0.14/0.38  # Paramodulations                      : 112
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 2
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 58
% 0.14/0.38  #    Positive orientable unit clauses  : 6
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 50
% 0.14/0.38  # Current number of unprocessed clauses: 42
% 0.14/0.38  # ...number of literals in the above   : 281
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 25
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 1130
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 97
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 49
% 0.14/0.38  # Unit Clause-clause subsumption calls : 14
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 3
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 7222
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.038 s
% 0.14/0.38  # System time              : 0.005 s
% 0.14/0.38  # Total time               : 0.043 s
% 0.14/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
