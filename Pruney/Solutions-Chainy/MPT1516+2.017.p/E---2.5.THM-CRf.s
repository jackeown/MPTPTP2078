%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:08 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  143 (111778 expanded)
%              Number of clauses        :  112 (39719 expanded)
%              Number of leaves         :   15 (26949 expanded)
%              Depth                    :   27
%              Number of atoms          :  666 (724892 expanded)
%              Number of equality atoms :  130 (72159 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(fraenkel_a_2_3_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v4_lattice3(X2)
        & l3_lattices(X2)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( r2_hidden(X1,a_2_3_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & r3_lattices(X2,X4,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_3_lattice3)).

fof(t46_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => ( r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
            & r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_lattice3)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(d17_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r4_lattice3(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X4,X3)
                   => r1_lattices(X1,X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

fof(d21_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2,X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
           => ( X3 = k15_lattice3(X1,X2)
            <=> ( r4_lattice3(X1,X3,X2)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r4_lattice3(X1,X4,X2)
                     => r1_lattices(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

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

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

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

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X39,X40,X41,X43] :
      ( ( m1_subset_1(esk8_3(X39,X40,X41),u1_struct_0(X40))
        | ~ r2_hidden(X39,a_2_3_lattice3(X40,X41))
        | v2_struct_0(X40)
        | ~ v10_lattices(X40)
        | ~ v4_lattice3(X40)
        | ~ l3_lattices(X40)
        | ~ m1_subset_1(X41,u1_struct_0(X40)) )
      & ( X39 = esk8_3(X39,X40,X41)
        | ~ r2_hidden(X39,a_2_3_lattice3(X40,X41))
        | v2_struct_0(X40)
        | ~ v10_lattices(X40)
        | ~ v4_lattice3(X40)
        | ~ l3_lattices(X40)
        | ~ m1_subset_1(X41,u1_struct_0(X40)) )
      & ( r3_lattices(X40,esk8_3(X39,X40,X41),X41)
        | ~ r2_hidden(X39,a_2_3_lattice3(X40,X41))
        | v2_struct_0(X40)
        | ~ v10_lattices(X40)
        | ~ v4_lattice3(X40)
        | ~ l3_lattices(X40)
        | ~ m1_subset_1(X41,u1_struct_0(X40)) )
      & ( ~ m1_subset_1(X43,u1_struct_0(X40))
        | X39 != X43
        | ~ r3_lattices(X40,X43,X41)
        | r2_hidden(X39,a_2_3_lattice3(X40,X41))
        | v2_struct_0(X40)
        | ~ v10_lattices(X40)
        | ~ v4_lattice3(X40)
        | ~ l3_lattices(X40)
        | ~ m1_subset_1(X41,u1_struct_0(X40)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_3_lattice3])])])])])])).

fof(c_0_17,plain,(
    ! [X46,X47,X48] :
      ( ( r3_lattices(X46,k15_lattice3(X46,X47),k15_lattice3(X46,X48))
        | ~ r1_tarski(X47,X48)
        | v2_struct_0(X46)
        | ~ v10_lattices(X46)
        | ~ v4_lattice3(X46)
        | ~ l3_lattices(X46) )
      & ( r3_lattices(X46,k16_lattice3(X46,X48),k16_lattice3(X46,X47))
        | ~ r1_tarski(X47,X48)
        | v2_struct_0(X46)
        | ~ v10_lattices(X46)
        | ~ v4_lattice3(X46)
        | ~ l3_lattices(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_lattice3])])])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk9_0)
    & v10_lattices(esk9_0)
    & v4_lattice3(esk9_0)
    & l3_lattices(esk9_0)
    & ( v2_struct_0(esk9_0)
      | ~ v10_lattices(esk9_0)
      | ~ v13_lattices(esk9_0)
      | ~ l3_lattices(esk9_0)
      | k5_lattices(esk9_0) != k15_lattice3(esk9_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,a_2_3_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattices(X2,X1,X4)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_tarski(X2,X3)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v4_lattice3(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( v10_lattices(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( l3_lattices(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_26,plain,(
    ! [X37,X38] :
      ( v2_struct_0(X37)
      | ~ l3_lattices(X37)
      | m1_subset_1(k15_lattice3(X37,X38),u1_struct_0(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_27,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( ~ r4_lattice3(X21,X22,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ r2_hidden(X24,X23)
        | r1_lattices(X21,X24,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( m1_subset_1(esk4_3(X21,X22,X25),u1_struct_0(X21))
        | r4_lattice3(X21,X22,X25)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( r2_hidden(esk4_3(X21,X22,X25),X25)
        | r4_lattice3(X21,X22,X25)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) )
      & ( ~ r1_lattices(X21,esk4_3(X21,X22,X25),X22)
        | r4_lattice3(X21,X22,X25)
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l3_lattices(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,a_2_3_lattice3(X2,X3))
    | v2_struct_0(X2)
    | ~ r3_lattices(X2,X1,X3)
    | ~ v4_lattice3(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( r3_lattices(esk9_0,k15_lattice3(esk9_0,X1),k15_lattice3(esk9_0,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X27,X28,X29,X30] :
      ( ( r4_lattice3(X27,X29,X28)
        | X29 != k15_lattice3(X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ v4_lattice3(X27)
        | ~ l3_lattices(X27)
        | v2_struct_0(X27)
        | ~ l3_lattices(X27) )
      & ( ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ r4_lattice3(X27,X30,X28)
        | r1_lattices(X27,X29,X30)
        | X29 != k15_lattice3(X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ v4_lattice3(X27)
        | ~ l3_lattices(X27)
        | v2_struct_0(X27)
        | ~ l3_lattices(X27) )
      & ( m1_subset_1(esk5_3(X27,X28,X29),u1_struct_0(X27))
        | ~ r4_lattice3(X27,X29,X28)
        | X29 = k15_lattice3(X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ v4_lattice3(X27)
        | ~ l3_lattices(X27)
        | v2_struct_0(X27)
        | ~ l3_lattices(X27) )
      & ( r4_lattice3(X27,esk5_3(X27,X28,X29),X28)
        | ~ r4_lattice3(X27,X29,X28)
        | X29 = k15_lattice3(X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ v4_lattice3(X27)
        | ~ l3_lattices(X27)
        | v2_struct_0(X27)
        | ~ l3_lattices(X27) )
      & ( ~ r1_lattices(X27,X29,esk5_3(X27,X28,X29))
        | ~ r4_lattice3(X27,X29,X28)
        | X29 = k15_lattice3(X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v10_lattices(X27)
        | ~ v4_lattice3(X27)
        | ~ l3_lattices(X27)
        | v2_struct_0(X27)
        | ~ l3_lattices(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

cnf(c_0_33,plain,
    ( r1_lattices(X1,X4,X2)
    | v2_struct_0(X1)
    | ~ r4_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,a_2_3_lattice3(esk9_0,X2))
    | ~ r3_lattices(esk9_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( r3_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k15_lattice3(esk9_0,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk9_0,X1),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_23]),c_0_24])).

cnf(c_0_37,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X1)
    | X2 != k15_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_38,plain,(
    ! [X44,X45] :
      ( ( X45 = k15_lattice3(X44,a_2_3_lattice3(X44,X45))
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ v10_lattices(X44)
        | ~ v4_lattice3(X44)
        | ~ l3_lattices(X44) )
      & ( X45 = k16_lattice3(X44,a_2_4_lattice3(X44,X45))
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ v10_lattices(X44)
        | ~ v4_lattice3(X44)
        | ~ l3_lattices(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).

fof(c_0_39,plain,(
    ! [X12] :
      ( ( l1_lattices(X12)
        | ~ l3_lattices(X12) )
      & ( l2_lattices(X12)
        | ~ l3_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_40,plain,(
    ! [X6] :
      ( ( ~ v2_struct_0(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v4_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v5_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v6_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v7_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v8_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( v9_lattices(X6)
        | v2_struct_0(X6)
        | ~ v10_lattices(X6)
        | ~ l3_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_41,negated_conjecture,
    ( r1_lattices(esk9_0,X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r4_lattice3(esk9_0,X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_23]),c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk9_0,k1_xboole_0),a_2_3_lattice3(esk9_0,k15_lattice3(esk9_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_36])])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | r4_lattice3(X1,X2,X3)
    | X2 != k15_lattice3(X1,X3)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( X1 = k15_lattice3(X2,a_2_3_lattice3(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_45,plain,(
    ! [X16,X18,X19] :
      ( ( m1_subset_1(esk2_1(X16),u1_struct_0(X16))
        | ~ v13_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) )
      & ( k2_lattices(X16,esk2_1(X16),X18) = esk2_1(X16)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ v13_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) )
      & ( k2_lattices(X16,X18,esk2_1(X16)) = esk2_1(X16)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ v13_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) )
      & ( m1_subset_1(esk3_2(X16,X19),u1_struct_0(X16))
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | v13_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) )
      & ( k2_lattices(X16,X19,esk3_2(X16,X19)) != X19
        | k2_lattices(X16,esk3_2(X16,X19),X19) != X19
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | v13_lattices(X16)
        | v2_struct_0(X16)
        | ~ l1_lattices(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

cnf(c_0_46,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_47,plain,(
    ! [X13,X14,X15] :
      ( ( ~ r1_lattices(X13,X14,X15)
        | k2_lattices(X13,X14,X15) = X14
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v8_lattices(X13)
        | ~ v9_lattices(X13)
        | ~ l3_lattices(X13) )
      & ( k2_lattices(X13,X14,X15) != X14
        | r1_lattices(X13,X14,X15)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v8_lattices(X13)
        | ~ v9_lattices(X13)
        | ~ l3_lattices(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_48,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( r1_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),X1)
    | ~ r4_lattice3(esk9_0,X1,a_2_3_lattice3(esk9_0,k15_lattice3(esk9_0,X2)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_36])])).

cnf(c_0_51,plain,
    ( r4_lattice3(X1,k15_lattice3(X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_43]),c_0_31])).

cnf(c_0_52,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,X1)) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

fof(c_0_53,plain,(
    ! [X32,X33,X34] :
      ( ( ~ v6_lattices(X32)
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | k2_lattices(X32,X33,X34) = k2_lattices(X32,X34,X33)
        | v2_struct_0(X32)
        | ~ l1_lattices(X32) )
      & ( m1_subset_1(esk6_1(X32),u1_struct_0(X32))
        | v6_lattices(X32)
        | v2_struct_0(X32)
        | ~ l1_lattices(X32) )
      & ( m1_subset_1(esk7_1(X32),u1_struct_0(X32))
        | v6_lattices(X32)
        | v2_struct_0(X32)
        | ~ l1_lattices(X32) )
      & ( k2_lattices(X32,esk6_1(X32),esk7_1(X32)) != k2_lattices(X32,esk7_1(X32),esk6_1(X32))
        | v6_lattices(X32)
        | v2_struct_0(X32)
        | ~ l1_lattices(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

cnf(c_0_54,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_55,plain,(
    ! [X11] :
      ( v2_struct_0(X11)
      | ~ l1_lattices(X11)
      | m1_subset_1(k5_lattices(X11),u1_struct_0(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_56,plain,(
    ! [X7,X8,X9] :
      ( ( k2_lattices(X7,X8,X9) = X8
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | X8 != k5_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v13_lattices(X7)
        | v2_struct_0(X7)
        | ~ l1_lattices(X7) )
      & ( k2_lattices(X7,X9,X8) = X8
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | X8 != k5_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v13_lattices(X7)
        | v2_struct_0(X7)
        | ~ l1_lattices(X7) )
      & ( m1_subset_1(esk1_2(X7,X8),u1_struct_0(X7))
        | X8 = k5_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v13_lattices(X7)
        | v2_struct_0(X7)
        | ~ l1_lattices(X7) )
      & ( k2_lattices(X7,X8,esk1_2(X7,X8)) != X8
        | k2_lattices(X7,esk1_2(X7,X8),X8) != X8
        | X8 = k5_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v13_lattices(X7)
        | v2_struct_0(X7)
        | ~ l1_lattices(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

cnf(c_0_57,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( l1_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_23])).

cnf(c_0_59,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,negated_conjecture,
    ( v9_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_61,negated_conjecture,
    ( v8_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_62,negated_conjecture,
    ( r1_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k15_lattice3(esk9_0,X1))
    | ~ r4_lattice3(esk9_0,k15_lattice3(esk9_0,X1),a_2_3_lattice3(esk9_0,k15_lattice3(esk9_0,X2))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_36])).

cnf(c_0_63,negated_conjecture,
    ( r4_lattice3(esk9_0,k15_lattice3(esk9_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_64,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,k15_lattice3(esk9_0,X1))) = k15_lattice3(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_36])).

cnf(c_0_65,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( v6_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk3_2(esk9_0,X1),u1_struct_0(esk9_0))
    | v13_lattices(esk9_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_24])).

cnf(c_0_70,negated_conjecture,
    ( k2_lattices(esk9_0,X1,X2) = X1
    | ~ r1_lattices(esk9_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_23])]),c_0_24])).

cnf(c_0_71,negated_conjecture,
    ( r1_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k15_lattice3(esk9_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( k2_lattices(esk9_0,X1,X2) = k2_lattices(esk9_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_58]),c_0_66])]),c_0_24])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk9_0),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_58]),c_0_24])).

cnf(c_0_74,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_68]),c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0))
    | v13_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_36])).

cnf(c_0_76,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k15_lattice3(esk9_0,X1)) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_36]),c_0_36])])).

cnf(c_0_77,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X3) != X2
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_78,negated_conjecture,
    ( k2_lattices(esk9_0,X1,k5_lattices(esk9_0)) = k2_lattices(esk9_0,k5_lattices(esk9_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k2_lattices(esk9_0,X1,k5_lattices(esk9_0)) = k5_lattices(esk9_0)
    | m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X2)),u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_58])]),c_0_24])).

cnf(c_0_80,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_81,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),k15_lattice3(esk9_0,k1_xboole_0)) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_76]),c_0_36]),c_0_36])])).

cnf(c_0_82,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,k5_lattices(esk9_0))) = k5_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_73])).

cnf(c_0_83,negated_conjecture,
    ( r1_lattices(esk9_0,X1,X2)
    | k2_lattices(esk9_0,X1,X2) != X1
    | ~ m1_subset_1(X2,u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_60]),c_0_61]),c_0_23])]),c_0_24])).

cnf(c_0_84,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),k5_lattices(esk9_0)) = k2_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,X1)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_36])).

cnf(c_0_85,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),k5_lattices(esk9_0)) = k5_lattices(esk9_0)
    | m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X2)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_36])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0))
    | m1_subset_1(esk2_1(esk9_0),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_75]),c_0_58])]),c_0_24])).

cnf(c_0_87,negated_conjecture,
    ( k2_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,k1_xboole_0)) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( r1_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,X1))
    | k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),k5_lattices(esk9_0)) != k5_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_36]),c_0_73])])).

cnf(c_0_89,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))) = esk3_2(esk9_0,k15_lattice3(esk9_0,X1))
    | k2_lattices(esk9_0,k15_lattice3(esk9_0,X2),k5_lattices(esk9_0)) = k5_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_85])).

cnf(c_0_90,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | k2_lattices(X1,esk3_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_91,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))) = esk3_2(esk9_0,k15_lattice3(esk9_0,X1))
    | m1_subset_1(esk2_1(esk9_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( k5_lattices(esk9_0) = k15_lattice3(esk9_0,k1_xboole_0)
    | ~ r1_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_87]),c_0_36]),c_0_73])])).

cnf(c_0_93,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))) = esk3_2(esk9_0,k15_lattice3(esk9_0,X1))
    | r1_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,X2)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( v13_lattices(esk9_0)
    | k2_lattices(esk9_0,X1,esk3_2(esk9_0,X1)) != X1
    | k2_lattices(esk9_0,esk3_2(esk9_0,X1),X1) != X1
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_58]),c_0_24])).

cnf(c_0_95,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))) = esk3_2(esk9_0,k15_lattice3(esk9_0,X1))
    | k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0))) = esk2_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))) = esk3_2(esk9_0,k15_lattice3(esk9_0,X1))
    | k5_lattices(esk9_0) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( v13_lattices(esk9_0)
    | k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),esk3_2(esk9_0,k15_lattice3(esk9_0,X1))) != k15_lattice3(esk9_0,X1)
    | k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),k15_lattice3(esk9_0,X1)) != k15_lattice3(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_36])).

cnf(c_0_98,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),esk3_2(esk9_0,k15_lattice3(esk9_0,X1))) = k15_lattice3(esk9_0,k1_xboole_0)
    | k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0))) = esk2_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),esk3_2(esk9_0,k15_lattice3(esk9_0,X1))) = k15_lattice3(esk9_0,k1_xboole_0)
    | k5_lattices(esk9_0) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( r3_lattices(esk9_0,k15_lattice3(esk9_0,X1),k5_lattices(esk9_0))
    | ~ r1_tarski(X1,a_2_3_lattice3(esk9_0,k5_lattices(esk9_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_82]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_101,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0))) = esk2_1(esk9_0)
    | v13_lattices(esk9_0)
    | k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)),k15_lattice3(esk9_0,k1_xboole_0)) != k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),k15_lattice3(esk9_0,k1_xboole_0)) = k15_lattice3(esk9_0,k1_xboole_0)
    | k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0))) = esk2_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( k5_lattices(esk9_0) = k15_lattice3(esk9_0,k1_xboole_0)
    | v13_lattices(esk9_0)
    | k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)),k15_lattice3(esk9_0,k1_xboole_0)) != k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),k15_lattice3(esk9_0,k1_xboole_0)) = k15_lattice3(esk9_0,k1_xboole_0)
    | k5_lattices(esk9_0) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( r3_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k5_lattices(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_30])).

cnf(c_0_106,plain,
    ( k2_lattices(X1,X2,esk2_1(X1)) = esk2_1(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_107,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0))) = esk2_1(esk9_0)
    | v13_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( k5_lattices(esk9_0) = k15_lattice3(esk9_0,k1_xboole_0)
    | v13_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(k15_lattice3(esk9_0,k1_xboole_0),a_2_3_lattice3(esk9_0,k5_lattices(esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_105]),c_0_73]),c_0_36])])).

cnf(c_0_110,negated_conjecture,
    ( k2_lattices(esk9_0,X1,esk2_1(esk9_0)) = esk2_1(esk9_0)
    | m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X2)),u1_struct_0(esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_75]),c_0_58])]),c_0_24])).

cnf(c_0_111,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0))) = esk2_1(esk9_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_107]),c_0_58])]),c_0_24]),c_0_52])).

cnf(c_0_112,negated_conjecture,
    ( k2_lattices(esk9_0,X1,esk2_1(esk9_0)) = esk2_1(esk9_0)
    | k5_lattices(esk9_0) = k15_lattice3(esk9_0,k1_xboole_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_108]),c_0_58])]),c_0_24])).

cnf(c_0_113,negated_conjecture,
    ( r1_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),X1)
    | ~ r4_lattice3(esk9_0,X1,a_2_3_lattice3(esk9_0,k5_lattices(esk9_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_109]),c_0_36])])).

cnf(c_0_114,negated_conjecture,
    ( r4_lattice3(esk9_0,k5_lattices(esk9_0),a_2_3_lattice3(esk9_0,k5_lattices(esk9_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_82]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_115,negated_conjecture,
    ( k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0)) = esk2_1(esk9_0)
    | m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_73])).

cnf(c_0_116,negated_conjecture,
    ( k2_lattices(esk9_0,X1,k5_lattices(esk9_0)) = k5_lattices(esk9_0)
    | k5_lattices(esk9_0) = k15_lattice3(esk9_0,k1_xboole_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_108]),c_0_58])]),c_0_24])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(esk2_1(esk9_0),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_111]),c_0_23])]),c_0_24])).

cnf(c_0_118,negated_conjecture,
    ( k2_lattices(esk9_0,esk2_1(esk9_0),k5_lattices(esk9_0)) = k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_111])).

cnf(c_0_119,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),esk2_1(esk9_0)) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_111])).

cnf(c_0_120,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),esk2_1(esk9_0)) = esk2_1(esk9_0)
    | k5_lattices(esk9_0) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_36])).

cnf(c_0_121,negated_conjecture,
    ( r1_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k5_lattices(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_73]),c_0_114])])).

cnf(c_0_122,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))) = esk3_2(esk9_0,k15_lattice3(esk9_0,X1))
    | k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0)) = esk2_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_115])).

cnf(c_0_123,negated_conjecture,
    ( v2_struct_0(esk9_0)
    | ~ v10_lattices(esk9_0)
    | ~ v13_lattices(esk9_0)
    | ~ l3_lattices(esk9_0)
    | k5_lattices(esk9_0) != k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_124,negated_conjecture,
    ( k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0)) = k5_lattices(esk9_0)
    | k5_lattices(esk9_0) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_118])).

cnf(c_0_125,negated_conjecture,
    ( k5_lattices(esk9_0) = k15_lattice3(esk9_0,k1_xboole_0)
    | esk2_1(esk9_0) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_126,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k5_lattices(esk9_0)) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_121]),c_0_73]),c_0_36])])).

cnf(c_0_127,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),esk3_2(esk9_0,k15_lattice3(esk9_0,X1))) = k15_lattice3(esk9_0,k1_xboole_0)
    | k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0)) = esk2_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_122])).

cnf(c_0_128,negated_conjecture,
    ( k5_lattices(esk9_0) != k15_lattice3(esk9_0,k1_xboole_0)
    | ~ v13_lattices(esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_23]),c_0_22])]),c_0_24])).

cnf(c_0_129,negated_conjecture,
    ( k5_lattices(esk9_0) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_84]),c_0_126])])).

cnf(c_0_130,negated_conjecture,
    ( k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0)) = esk2_1(esk9_0)
    | v13_lattices(esk9_0)
    | k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)),k15_lattice3(esk9_0,k1_xboole_0)) != k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_127])).

cnf(c_0_131,negated_conjecture,
    ( k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),k15_lattice3(esk9_0,k1_xboole_0)) = k15_lattice3(esk9_0,k1_xboole_0)
    | k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0)) = esk2_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_122])).

cnf(c_0_132,negated_conjecture,
    ( ~ v13_lattices(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_129])])).

cnf(c_0_133,negated_conjecture,
    ( k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0)) = esk2_1(esk9_0)
    | v13_lattices(esk9_0) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_134,negated_conjecture,
    ( m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0)) ),
    inference(sr,[status(thm)],[c_0_75,c_0_132])).

cnf(c_0_135,negated_conjecture,
    ( v13_lattices(esk9_0)
    | k2_lattices(esk9_0,esk2_1(esk9_0),esk3_2(esk9_0,esk2_1(esk9_0))) != esk2_1(esk9_0)
    | k2_lattices(esk9_0,esk3_2(esk9_0,esk2_1(esk9_0)),esk2_1(esk9_0)) != esk2_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_111])).

cnf(c_0_136,negated_conjecture,
    ( esk2_1(esk9_0) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_129]),c_0_119]),c_0_132])).

cnf(c_0_137,negated_conjecture,
    ( k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))) = esk3_2(esk9_0,k15_lattice3(esk9_0,X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_134])).

cnf(c_0_138,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),esk3_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0))) != k15_lattice3(esk9_0,k1_xboole_0)
    | k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)),k15_lattice3(esk9_0,k1_xboole_0)) != k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_136]),c_0_136]),c_0_136]),c_0_136]),c_0_136]),c_0_136]),c_0_132])).

cnf(c_0_139,negated_conjecture,
    ( k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),esk3_2(esk9_0,k15_lattice3(esk9_0,X1))) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_137])).

cnf(c_0_140,negated_conjecture,
    ( k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)),k15_lattice3(esk9_0,k1_xboole_0)) != k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_138,c_0_139])])).

cnf(c_0_141,negated_conjecture,
    ( k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),k15_lattice3(esk9_0,k1_xboole_0)) = k15_lattice3(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_137])).

cnf(c_0_142,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_140,c_0_141])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:46:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.92/1.10  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 0.92/1.10  # and selection function HSelectMinInfpos.
% 0.92/1.10  #
% 0.92/1.10  # Preprocessing time       : 0.031 s
% 0.92/1.10  # Presaturation interreduction done
% 0.92/1.10  
% 0.92/1.10  # Proof found!
% 0.92/1.10  # SZS status Theorem
% 0.92/1.10  # SZS output start CNFRefutation
% 0.92/1.10  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_lattice3)).
% 0.92/1.10  fof(fraenkel_a_2_3_lattice3, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))&m1_subset_1(X3,u1_struct_0(X2)))=>(r2_hidden(X1,a_2_3_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r3_lattices(X2,X4,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_3_lattice3)).
% 0.92/1.10  fof(t46_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(r1_tarski(X2,X3)=>(r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))&r3_lattices(X1,k16_lattice3(X1,X3),k16_lattice3(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_lattice3)).
% 0.92/1.10  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.92/1.10  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.92/1.10  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 0.92/1.10  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 0.92/1.10  fof(t45_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k15_lattice3(X1,a_2_3_lattice3(X1,X2))&X2=k16_lattice3(X1,a_2_4_lattice3(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_lattice3)).
% 0.92/1.10  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.92/1.10  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.92/1.10  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_lattices)).
% 0.92/1.10  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 0.92/1.10  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_lattices)).
% 0.92/1.10  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.92/1.10  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 0.92/1.10  fof(c_0_15, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 0.92/1.10  fof(c_0_16, plain, ![X39, X40, X41, X43]:((((m1_subset_1(esk8_3(X39,X40,X41),u1_struct_0(X40))|~r2_hidden(X39,a_2_3_lattice3(X40,X41))|(v2_struct_0(X40)|~v10_lattices(X40)|~v4_lattice3(X40)|~l3_lattices(X40)|~m1_subset_1(X41,u1_struct_0(X40))))&(X39=esk8_3(X39,X40,X41)|~r2_hidden(X39,a_2_3_lattice3(X40,X41))|(v2_struct_0(X40)|~v10_lattices(X40)|~v4_lattice3(X40)|~l3_lattices(X40)|~m1_subset_1(X41,u1_struct_0(X40)))))&(r3_lattices(X40,esk8_3(X39,X40,X41),X41)|~r2_hidden(X39,a_2_3_lattice3(X40,X41))|(v2_struct_0(X40)|~v10_lattices(X40)|~v4_lattice3(X40)|~l3_lattices(X40)|~m1_subset_1(X41,u1_struct_0(X40)))))&(~m1_subset_1(X43,u1_struct_0(X40))|X39!=X43|~r3_lattices(X40,X43,X41)|r2_hidden(X39,a_2_3_lattice3(X40,X41))|(v2_struct_0(X40)|~v10_lattices(X40)|~v4_lattice3(X40)|~l3_lattices(X40)|~m1_subset_1(X41,u1_struct_0(X40))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_3_lattice3])])])])])])).
% 0.92/1.10  fof(c_0_17, plain, ![X46, X47, X48]:((r3_lattices(X46,k15_lattice3(X46,X47),k15_lattice3(X46,X48))|~r1_tarski(X47,X48)|(v2_struct_0(X46)|~v10_lattices(X46)|~v4_lattice3(X46)|~l3_lattices(X46)))&(r3_lattices(X46,k16_lattice3(X46,X48),k16_lattice3(X46,X47))|~r1_tarski(X47,X48)|(v2_struct_0(X46)|~v10_lattices(X46)|~v4_lattice3(X46)|~l3_lattices(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_lattice3])])])])])).
% 0.92/1.10  fof(c_0_18, negated_conjecture, ((((~v2_struct_0(esk9_0)&v10_lattices(esk9_0))&v4_lattice3(esk9_0))&l3_lattices(esk9_0))&(v2_struct_0(esk9_0)|~v10_lattices(esk9_0)|~v13_lattices(esk9_0)|~l3_lattices(esk9_0)|k5_lattices(esk9_0)!=k15_lattice3(esk9_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.92/1.10  cnf(c_0_19, plain, (r2_hidden(X3,a_2_3_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r3_lattices(X2,X1,X4)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~m1_subset_1(X4,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.92/1.10  cnf(c_0_20, plain, (r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~r1_tarski(X2,X3)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.92/1.10  cnf(c_0_21, negated_conjecture, (v4_lattice3(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.92/1.10  cnf(c_0_22, negated_conjecture, (v10_lattices(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.92/1.10  cnf(c_0_23, negated_conjecture, (l3_lattices(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.92/1.10  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.92/1.10  fof(c_0_25, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.92/1.10  fof(c_0_26, plain, ![X37, X38]:(v2_struct_0(X37)|~l3_lattices(X37)|m1_subset_1(k15_lattice3(X37,X38),u1_struct_0(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.92/1.10  fof(c_0_27, plain, ![X21, X22, X23, X24, X25]:((~r4_lattice3(X21,X22,X23)|(~m1_subset_1(X24,u1_struct_0(X21))|(~r2_hidden(X24,X23)|r1_lattices(X21,X24,X22)))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&((m1_subset_1(esk4_3(X21,X22,X25),u1_struct_0(X21))|r4_lattice3(X21,X22,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&((r2_hidden(esk4_3(X21,X22,X25),X25)|r4_lattice3(X21,X22,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))&(~r1_lattices(X21,esk4_3(X21,X22,X25),X22)|r4_lattice3(X21,X22,X25)|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l3_lattices(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.92/1.10  cnf(c_0_28, plain, (r2_hidden(X1,a_2_3_lattice3(X2,X3))|v2_struct_0(X2)|~r3_lattices(X2,X1,X3)|~v4_lattice3(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)), inference(er,[status(thm)],[c_0_19])).
% 0.92/1.10  cnf(c_0_29, negated_conjecture, (r3_lattices(esk9_0,k15_lattice3(esk9_0,X1),k15_lattice3(esk9_0,X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.92/1.10  cnf(c_0_30, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.92/1.10  cnf(c_0_31, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.92/1.10  fof(c_0_32, plain, ![X27, X28, X29, X30]:(((r4_lattice3(X27,X29,X28)|X29!=k15_lattice3(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27))|(v2_struct_0(X27)|~l3_lattices(X27)))&(~m1_subset_1(X30,u1_struct_0(X27))|(~r4_lattice3(X27,X30,X28)|r1_lattices(X27,X29,X30))|X29!=k15_lattice3(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27))|(v2_struct_0(X27)|~l3_lattices(X27))))&((m1_subset_1(esk5_3(X27,X28,X29),u1_struct_0(X27))|~r4_lattice3(X27,X29,X28)|X29=k15_lattice3(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27))|(v2_struct_0(X27)|~l3_lattices(X27)))&((r4_lattice3(X27,esk5_3(X27,X28,X29),X28)|~r4_lattice3(X27,X29,X28)|X29=k15_lattice3(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27))|(v2_struct_0(X27)|~l3_lattices(X27)))&(~r1_lattices(X27,X29,esk5_3(X27,X28,X29))|~r4_lattice3(X27,X29,X28)|X29=k15_lattice3(X27,X28)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X27)|~v10_lattices(X27)|~v4_lattice3(X27)|~l3_lattices(X27))|(v2_struct_0(X27)|~l3_lattices(X27)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.92/1.10  cnf(c_0_33, plain, (r1_lattices(X1,X4,X2)|v2_struct_0(X1)|~r4_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.92/1.10  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,a_2_3_lattice3(esk9_0,X2))|~r3_lattices(esk9_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.92/1.10  cnf(c_0_35, negated_conjecture, (r3_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k15_lattice3(esk9_0,X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.92/1.10  cnf(c_0_36, negated_conjecture, (m1_subset_1(k15_lattice3(esk9_0,X1),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_23]), c_0_24])).
% 0.92/1.10  cnf(c_0_37, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X1)|X2!=k15_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.92/1.10  fof(c_0_38, plain, ![X44, X45]:((X45=k15_lattice3(X44,a_2_3_lattice3(X44,X45))|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~v10_lattices(X44)|~v4_lattice3(X44)|~l3_lattices(X44)))&(X45=k16_lattice3(X44,a_2_4_lattice3(X44,X45))|~m1_subset_1(X45,u1_struct_0(X44))|(v2_struct_0(X44)|~v10_lattices(X44)|~v4_lattice3(X44)|~l3_lattices(X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).
% 0.92/1.10  fof(c_0_39, plain, ![X12]:((l1_lattices(X12)|~l3_lattices(X12))&(l2_lattices(X12)|~l3_lattices(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.92/1.10  fof(c_0_40, plain, ![X6]:(((((((~v2_struct_0(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6))&(v4_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v5_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v6_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v7_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v8_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6)))&(v9_lattices(X6)|(v2_struct_0(X6)|~v10_lattices(X6))|~l3_lattices(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.92/1.10  cnf(c_0_41, negated_conjecture, (r1_lattices(esk9_0,X1,X2)|~r2_hidden(X1,X3)|~r4_lattice3(esk9_0,X2,X3)|~m1_subset_1(X1,u1_struct_0(esk9_0))|~m1_subset_1(X2,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_23]), c_0_24])).
% 0.92/1.10  cnf(c_0_42, negated_conjecture, (r2_hidden(k15_lattice3(esk9_0,k1_xboole_0),a_2_3_lattice3(esk9_0,k15_lattice3(esk9_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_36])])).
% 0.92/1.10  cnf(c_0_43, plain, (v2_struct_0(X1)|r4_lattice3(X1,X2,X3)|X2!=k15_lattice3(X1,X3)|~l3_lattices(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[c_0_37])).
% 0.92/1.10  cnf(c_0_44, plain, (X1=k15_lattice3(X2,a_2_3_lattice3(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.92/1.10  fof(c_0_45, plain, ![X16, X18, X19]:(((m1_subset_1(esk2_1(X16),u1_struct_0(X16))|~v13_lattices(X16)|(v2_struct_0(X16)|~l1_lattices(X16)))&((k2_lattices(X16,esk2_1(X16),X18)=esk2_1(X16)|~m1_subset_1(X18,u1_struct_0(X16))|~v13_lattices(X16)|(v2_struct_0(X16)|~l1_lattices(X16)))&(k2_lattices(X16,X18,esk2_1(X16))=esk2_1(X16)|~m1_subset_1(X18,u1_struct_0(X16))|~v13_lattices(X16)|(v2_struct_0(X16)|~l1_lattices(X16)))))&((m1_subset_1(esk3_2(X16,X19),u1_struct_0(X16))|~m1_subset_1(X19,u1_struct_0(X16))|v13_lattices(X16)|(v2_struct_0(X16)|~l1_lattices(X16)))&(k2_lattices(X16,X19,esk3_2(X16,X19))!=X19|k2_lattices(X16,esk3_2(X16,X19),X19)!=X19|~m1_subset_1(X19,u1_struct_0(X16))|v13_lattices(X16)|(v2_struct_0(X16)|~l1_lattices(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 0.92/1.10  cnf(c_0_46, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.92/1.10  fof(c_0_47, plain, ![X13, X14, X15]:((~r1_lattices(X13,X14,X15)|k2_lattices(X13,X14,X15)=X14|~m1_subset_1(X15,u1_struct_0(X13))|~m1_subset_1(X14,u1_struct_0(X13))|(v2_struct_0(X13)|~v8_lattices(X13)|~v9_lattices(X13)|~l3_lattices(X13)))&(k2_lattices(X13,X14,X15)!=X14|r1_lattices(X13,X14,X15)|~m1_subset_1(X15,u1_struct_0(X13))|~m1_subset_1(X14,u1_struct_0(X13))|(v2_struct_0(X13)|~v8_lattices(X13)|~v9_lattices(X13)|~l3_lattices(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.92/1.10  cnf(c_0_48, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.92/1.10  cnf(c_0_49, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.92/1.10  cnf(c_0_50, negated_conjecture, (r1_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),X1)|~r4_lattice3(esk9_0,X1,a_2_3_lattice3(esk9_0,k15_lattice3(esk9_0,X2)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_36])])).
% 0.92/1.10  cnf(c_0_51, plain, (r4_lattice3(X1,k15_lattice3(X1,X2),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_43]), c_0_31])).
% 0.92/1.10  cnf(c_0_52, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,X1))=X1|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.92/1.10  fof(c_0_53, plain, ![X32, X33, X34]:((~v6_lattices(X32)|(~m1_subset_1(X33,u1_struct_0(X32))|(~m1_subset_1(X34,u1_struct_0(X32))|k2_lattices(X32,X33,X34)=k2_lattices(X32,X34,X33)))|(v2_struct_0(X32)|~l1_lattices(X32)))&((m1_subset_1(esk6_1(X32),u1_struct_0(X32))|v6_lattices(X32)|(v2_struct_0(X32)|~l1_lattices(X32)))&((m1_subset_1(esk7_1(X32),u1_struct_0(X32))|v6_lattices(X32)|(v2_struct_0(X32)|~l1_lattices(X32)))&(k2_lattices(X32,esk6_1(X32),esk7_1(X32))!=k2_lattices(X32,esk7_1(X32),esk6_1(X32))|v6_lattices(X32)|(v2_struct_0(X32)|~l1_lattices(X32)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 0.92/1.10  cnf(c_0_54, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.92/1.10  fof(c_0_55, plain, ![X11]:(v2_struct_0(X11)|~l1_lattices(X11)|m1_subset_1(k5_lattices(X11),u1_struct_0(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.92/1.10  fof(c_0_56, plain, ![X7, X8, X9]:(((k2_lattices(X7,X8,X9)=X8|~m1_subset_1(X9,u1_struct_0(X7))|X8!=k5_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~v13_lattices(X7)|(v2_struct_0(X7)|~l1_lattices(X7)))&(k2_lattices(X7,X9,X8)=X8|~m1_subset_1(X9,u1_struct_0(X7))|X8!=k5_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~v13_lattices(X7)|(v2_struct_0(X7)|~l1_lattices(X7))))&((m1_subset_1(esk1_2(X7,X8),u1_struct_0(X7))|X8=k5_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~v13_lattices(X7)|(v2_struct_0(X7)|~l1_lattices(X7)))&(k2_lattices(X7,X8,esk1_2(X7,X8))!=X8|k2_lattices(X7,esk1_2(X7,X8),X8)!=X8|X8=k5_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~v13_lattices(X7)|(v2_struct_0(X7)|~l1_lattices(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.92/1.10  cnf(c_0_57, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.92/1.10  cnf(c_0_58, negated_conjecture, (l1_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_46, c_0_23])).
% 0.92/1.10  cnf(c_0_59, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.92/1.10  cnf(c_0_60, negated_conjecture, (v9_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_22]), c_0_23])]), c_0_24])).
% 0.92/1.10  cnf(c_0_61, negated_conjecture, (v8_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_22]), c_0_23])]), c_0_24])).
% 0.92/1.10  cnf(c_0_62, negated_conjecture, (r1_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k15_lattice3(esk9_0,X1))|~r4_lattice3(esk9_0,k15_lattice3(esk9_0,X1),a_2_3_lattice3(esk9_0,k15_lattice3(esk9_0,X2)))), inference(spm,[status(thm)],[c_0_50, c_0_36])).
% 0.92/1.10  cnf(c_0_63, negated_conjecture, (r4_lattice3(esk9_0,k15_lattice3(esk9_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.92/1.10  cnf(c_0_64, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,k15_lattice3(esk9_0,X1)))=k15_lattice3(esk9_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_36])).
% 0.92/1.10  cnf(c_0_65, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.92/1.10  cnf(c_0_66, negated_conjecture, (v6_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_22]), c_0_23])]), c_0_24])).
% 0.92/1.10  cnf(c_0_67, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.92/1.10  cnf(c_0_68, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.92/1.10  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk3_2(esk9_0,X1),u1_struct_0(esk9_0))|v13_lattices(esk9_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_24])).
% 0.92/1.10  cnf(c_0_70, negated_conjecture, (k2_lattices(esk9_0,X1,X2)=X1|~r1_lattices(esk9_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_23])]), c_0_24])).
% 0.92/1.10  cnf(c_0_71, negated_conjecture, (r1_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k15_lattice3(esk9_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.92/1.10  cnf(c_0_72, negated_conjecture, (k2_lattices(esk9_0,X1,X2)=k2_lattices(esk9_0,X2,X1)|~m1_subset_1(X2,u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_58]), c_0_66])]), c_0_24])).
% 0.92/1.10  cnf(c_0_73, negated_conjecture, (m1_subset_1(k5_lattices(esk9_0),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_58]), c_0_24])).
% 0.92/1.10  cnf(c_0_74, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_68]), c_0_67])).
% 0.92/1.10  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0))|v13_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_69, c_0_36])).
% 0.92/1.10  cnf(c_0_76, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k15_lattice3(esk9_0,X1))=k15_lattice3(esk9_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_36]), c_0_36])])).
% 0.92/1.10  cnf(c_0_77, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k2_lattices(X1,X2,X3)!=X2|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.92/1.10  cnf(c_0_78, negated_conjecture, (k2_lattices(esk9_0,X1,k5_lattices(esk9_0))=k2_lattices(esk9_0,k5_lattices(esk9_0),X1)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.92/1.10  cnf(c_0_79, negated_conjecture, (k2_lattices(esk9_0,X1,k5_lattices(esk9_0))=k5_lattices(esk9_0)|m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X2)),u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_58])]), c_0_24])).
% 0.92/1.10  cnf(c_0_80, plain, (m1_subset_1(esk2_1(X1),u1_struct_0(X1))|v2_struct_0(X1)|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.92/1.10  cnf(c_0_81, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),k15_lattice3(esk9_0,k1_xboole_0))=k15_lattice3(esk9_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_76]), c_0_36]), c_0_36])])).
% 0.92/1.10  cnf(c_0_82, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,k5_lattices(esk9_0)))=k5_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_52, c_0_73])).
% 0.92/1.10  cnf(c_0_83, negated_conjecture, (r1_lattices(esk9_0,X1,X2)|k2_lattices(esk9_0,X1,X2)!=X1|~m1_subset_1(X2,u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_60]), c_0_61]), c_0_23])]), c_0_24])).
% 0.92/1.10  cnf(c_0_84, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),k5_lattices(esk9_0))=k2_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,X1))), inference(spm,[status(thm)],[c_0_78, c_0_36])).
% 0.92/1.10  cnf(c_0_85, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),k5_lattices(esk9_0))=k5_lattices(esk9_0)|m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X2)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_79, c_0_36])).
% 0.92/1.10  cnf(c_0_86, negated_conjecture, (m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0))|m1_subset_1(esk2_1(esk9_0),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_75]), c_0_58])]), c_0_24])).
% 0.92/1.10  cnf(c_0_87, negated_conjecture, (k2_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,k1_xboole_0))=k15_lattice3(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.92/1.10  cnf(c_0_88, negated_conjecture, (r1_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,X1))|k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),k5_lattices(esk9_0))!=k5_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_36]), c_0_73])])).
% 0.92/1.10  cnf(c_0_89, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1))))=esk3_2(esk9_0,k15_lattice3(esk9_0,X1))|k2_lattices(esk9_0,k15_lattice3(esk9_0,X2),k5_lattices(esk9_0))=k5_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_52, c_0_85])).
% 0.92/1.10  cnf(c_0_90, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|k2_lattices(X1,esk3_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.92/1.10  cnf(c_0_91, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1))))=esk3_2(esk9_0,k15_lattice3(esk9_0,X1))|m1_subset_1(esk2_1(esk9_0),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_52, c_0_86])).
% 0.92/1.10  cnf(c_0_92, negated_conjecture, (k5_lattices(esk9_0)=k15_lattice3(esk9_0,k1_xboole_0)|~r1_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_87]), c_0_36]), c_0_73])])).
% 0.92/1.10  cnf(c_0_93, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1))))=esk3_2(esk9_0,k15_lattice3(esk9_0,X1))|r1_lattices(esk9_0,k5_lattices(esk9_0),k15_lattice3(esk9_0,X2))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.92/1.10  cnf(c_0_94, negated_conjecture, (v13_lattices(esk9_0)|k2_lattices(esk9_0,X1,esk3_2(esk9_0,X1))!=X1|k2_lattices(esk9_0,esk3_2(esk9_0,X1),X1)!=X1|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_58]), c_0_24])).
% 0.92/1.10  cnf(c_0_95, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1))))=esk3_2(esk9_0,k15_lattice3(esk9_0,X1))|k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0)))=esk2_1(esk9_0)), inference(spm,[status(thm)],[c_0_52, c_0_91])).
% 0.92/1.10  cnf(c_0_96, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1))))=esk3_2(esk9_0,k15_lattice3(esk9_0,X1))|k5_lattices(esk9_0)=k15_lattice3(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.92/1.10  cnf(c_0_97, negated_conjecture, (v13_lattices(esk9_0)|k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))!=k15_lattice3(esk9_0,X1)|k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),k15_lattice3(esk9_0,X1))!=k15_lattice3(esk9_0,X1)), inference(spm,[status(thm)],[c_0_94, c_0_36])).
% 0.92/1.10  cnf(c_0_98, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))=k15_lattice3(esk9_0,k1_xboole_0)|k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0)))=esk2_1(esk9_0)), inference(spm,[status(thm)],[c_0_76, c_0_95])).
% 0.92/1.10  cnf(c_0_99, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))=k15_lattice3(esk9_0,k1_xboole_0)|k5_lattices(esk9_0)=k15_lattice3(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_76, c_0_96])).
% 0.92/1.10  cnf(c_0_100, negated_conjecture, (r3_lattices(esk9_0,k15_lattice3(esk9_0,X1),k5_lattices(esk9_0))|~r1_tarski(X1,a_2_3_lattice3(esk9_0,k5_lattices(esk9_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_82]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.92/1.10  cnf(c_0_101, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0)))=esk2_1(esk9_0)|v13_lattices(esk9_0)|k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)),k15_lattice3(esk9_0,k1_xboole_0))!=k15_lattice3(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.92/1.10  cnf(c_0_102, negated_conjecture, (k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),k15_lattice3(esk9_0,k1_xboole_0))=k15_lattice3(esk9_0,k1_xboole_0)|k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0)))=esk2_1(esk9_0)), inference(spm,[status(thm)],[c_0_81, c_0_95])).
% 0.92/1.10  cnf(c_0_103, negated_conjecture, (k5_lattices(esk9_0)=k15_lattice3(esk9_0,k1_xboole_0)|v13_lattices(esk9_0)|k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)),k15_lattice3(esk9_0,k1_xboole_0))!=k15_lattice3(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_97, c_0_99])).
% 0.92/1.10  cnf(c_0_104, negated_conjecture, (k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),k15_lattice3(esk9_0,k1_xboole_0))=k15_lattice3(esk9_0,k1_xboole_0)|k5_lattices(esk9_0)=k15_lattice3(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_81, c_0_96])).
% 0.92/1.10  cnf(c_0_105, negated_conjecture, (r3_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k5_lattices(esk9_0))), inference(spm,[status(thm)],[c_0_100, c_0_30])).
% 0.92/1.10  cnf(c_0_106, plain, (k2_lattices(X1,X2,esk2_1(X1))=esk2_1(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.92/1.10  cnf(c_0_107, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0)))=esk2_1(esk9_0)|v13_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.92/1.10  cnf(c_0_108, negated_conjecture, (k5_lattices(esk9_0)=k15_lattice3(esk9_0,k1_xboole_0)|v13_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.92/1.10  cnf(c_0_109, negated_conjecture, (r2_hidden(k15_lattice3(esk9_0,k1_xboole_0),a_2_3_lattice3(esk9_0,k5_lattices(esk9_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_105]), c_0_73]), c_0_36])])).
% 0.92/1.10  cnf(c_0_110, negated_conjecture, (k2_lattices(esk9_0,X1,esk2_1(esk9_0))=esk2_1(esk9_0)|m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X2)),u1_struct_0(esk9_0))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_75]), c_0_58])]), c_0_24])).
% 0.92/1.10  cnf(c_0_111, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk2_1(esk9_0)))=esk2_1(esk9_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_107]), c_0_58])]), c_0_24]), c_0_52])).
% 0.92/1.10  cnf(c_0_112, negated_conjecture, (k2_lattices(esk9_0,X1,esk2_1(esk9_0))=esk2_1(esk9_0)|k5_lattices(esk9_0)=k15_lattice3(esk9_0,k1_xboole_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_108]), c_0_58])]), c_0_24])).
% 0.92/1.10  cnf(c_0_113, negated_conjecture, (r1_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),X1)|~r4_lattice3(esk9_0,X1,a_2_3_lattice3(esk9_0,k5_lattices(esk9_0)))|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_109]), c_0_36])])).
% 0.92/1.10  cnf(c_0_114, negated_conjecture, (r4_lattice3(esk9_0,k5_lattices(esk9_0),a_2_3_lattice3(esk9_0,k5_lattices(esk9_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_82]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.92/1.10  cnf(c_0_115, negated_conjecture, (k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0))=esk2_1(esk9_0)|m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_110, c_0_73])).
% 0.92/1.10  cnf(c_0_116, negated_conjecture, (k2_lattices(esk9_0,X1,k5_lattices(esk9_0))=k5_lattices(esk9_0)|k5_lattices(esk9_0)=k15_lattice3(esk9_0,k1_xboole_0)|~m1_subset_1(X1,u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_108]), c_0_58])]), c_0_24])).
% 0.92/1.10  cnf(c_0_117, negated_conjecture, (m1_subset_1(esk2_1(esk9_0),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_111]), c_0_23])]), c_0_24])).
% 0.92/1.10  cnf(c_0_118, negated_conjecture, (k2_lattices(esk9_0,esk2_1(esk9_0),k5_lattices(esk9_0))=k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0))), inference(spm,[status(thm)],[c_0_84, c_0_111])).
% 0.92/1.10  cnf(c_0_119, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),esk2_1(esk9_0))=k15_lattice3(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_76, c_0_111])).
% 0.92/1.10  cnf(c_0_120, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,X1),esk2_1(esk9_0))=esk2_1(esk9_0)|k5_lattices(esk9_0)=k15_lattice3(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_112, c_0_36])).
% 0.92/1.10  cnf(c_0_121, negated_conjecture, (r1_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k5_lattices(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_73]), c_0_114])])).
% 0.92/1.10  cnf(c_0_122, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1))))=esk3_2(esk9_0,k15_lattice3(esk9_0,X1))|k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0))=esk2_1(esk9_0)), inference(spm,[status(thm)],[c_0_52, c_0_115])).
% 0.92/1.10  cnf(c_0_123, negated_conjecture, (v2_struct_0(esk9_0)|~v10_lattices(esk9_0)|~v13_lattices(esk9_0)|~l3_lattices(esk9_0)|k5_lattices(esk9_0)!=k15_lattice3(esk9_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.92/1.10  cnf(c_0_124, negated_conjecture, (k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0))=k5_lattices(esk9_0)|k5_lattices(esk9_0)=k15_lattice3(esk9_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_118])).
% 0.92/1.10  cnf(c_0_125, negated_conjecture, (k5_lattices(esk9_0)=k15_lattice3(esk9_0,k1_xboole_0)|esk2_1(esk9_0)=k15_lattice3(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_119, c_0_120])).
% 0.92/1.10  cnf(c_0_126, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),k5_lattices(esk9_0))=k15_lattice3(esk9_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_121]), c_0_73]), c_0_36])])).
% 0.92/1.10  cnf(c_0_127, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))=k15_lattice3(esk9_0,k1_xboole_0)|k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0))=esk2_1(esk9_0)), inference(spm,[status(thm)],[c_0_76, c_0_122])).
% 0.92/1.10  cnf(c_0_128, negated_conjecture, (k5_lattices(esk9_0)!=k15_lattice3(esk9_0,k1_xboole_0)|~v13_lattices(esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_23]), c_0_22])]), c_0_24])).
% 0.92/1.10  cnf(c_0_129, negated_conjecture, (k5_lattices(esk9_0)=k15_lattice3(esk9_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_84]), c_0_126])])).
% 0.92/1.10  cnf(c_0_130, negated_conjecture, (k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0))=esk2_1(esk9_0)|v13_lattices(esk9_0)|k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)),k15_lattice3(esk9_0,k1_xboole_0))!=k15_lattice3(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_97, c_0_127])).
% 0.92/1.10  cnf(c_0_131, negated_conjecture, (k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),k15_lattice3(esk9_0,k1_xboole_0))=k15_lattice3(esk9_0,k1_xboole_0)|k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0))=esk2_1(esk9_0)), inference(spm,[status(thm)],[c_0_81, c_0_122])).
% 0.92/1.10  cnf(c_0_132, negated_conjecture, (~v13_lattices(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_129])])).
% 0.92/1.10  cnf(c_0_133, negated_conjecture, (k2_lattices(esk9_0,k5_lattices(esk9_0),esk2_1(esk9_0))=esk2_1(esk9_0)|v13_lattices(esk9_0)), inference(spm,[status(thm)],[c_0_130, c_0_131])).
% 0.92/1.10  cnf(c_0_134, negated_conjecture, (m1_subset_1(esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),u1_struct_0(esk9_0))), inference(sr,[status(thm)],[c_0_75, c_0_132])).
% 0.92/1.10  cnf(c_0_135, negated_conjecture, (v13_lattices(esk9_0)|k2_lattices(esk9_0,esk2_1(esk9_0),esk3_2(esk9_0,esk2_1(esk9_0)))!=esk2_1(esk9_0)|k2_lattices(esk9_0,esk3_2(esk9_0,esk2_1(esk9_0)),esk2_1(esk9_0))!=esk2_1(esk9_0)), inference(spm,[status(thm)],[c_0_97, c_0_111])).
% 0.92/1.10  cnf(c_0_136, negated_conjecture, (esk2_1(esk9_0)=k15_lattice3(esk9_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133, c_0_129]), c_0_119]), c_0_132])).
% 0.92/1.10  cnf(c_0_137, negated_conjecture, (k15_lattice3(esk9_0,a_2_3_lattice3(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1))))=esk3_2(esk9_0,k15_lattice3(esk9_0,X1))), inference(spm,[status(thm)],[c_0_52, c_0_134])).
% 0.92/1.10  cnf(c_0_138, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),esk3_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)))!=k15_lattice3(esk9_0,k1_xboole_0)|k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)),k15_lattice3(esk9_0,k1_xboole_0))!=k15_lattice3(esk9_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_136]), c_0_136]), c_0_136]), c_0_136]), c_0_136]), c_0_136]), c_0_132])).
% 0.92/1.10  cnf(c_0_139, negated_conjecture, (k2_lattices(esk9_0,k15_lattice3(esk9_0,k1_xboole_0),esk3_2(esk9_0,k15_lattice3(esk9_0,X1)))=k15_lattice3(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_76, c_0_137])).
% 0.92/1.10  cnf(c_0_140, negated_conjecture, (k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,k1_xboole_0)),k15_lattice3(esk9_0,k1_xboole_0))!=k15_lattice3(esk9_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_138, c_0_139])])).
% 0.92/1.10  cnf(c_0_141, negated_conjecture, (k2_lattices(esk9_0,esk3_2(esk9_0,k15_lattice3(esk9_0,X1)),k15_lattice3(esk9_0,k1_xboole_0))=k15_lattice3(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_81, c_0_137])).
% 0.92/1.10  cnf(c_0_142, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_140, c_0_141])]), ['proof']).
% 0.92/1.10  # SZS output end CNFRefutation
% 0.92/1.10  # Proof object total steps             : 143
% 0.92/1.10  # Proof object clause steps            : 112
% 0.92/1.10  # Proof object formula steps           : 31
% 0.92/1.10  # Proof object conjectures             : 91
% 0.92/1.10  # Proof object clause conjectures      : 88
% 0.92/1.10  # Proof object formula conjectures     : 3
% 0.92/1.10  # Proof object initial clauses used    : 25
% 0.92/1.10  # Proof object initial formulas used   : 15
% 0.92/1.10  # Proof object generating inferences   : 76
% 0.92/1.10  # Proof object simplifying inferences  : 132
% 0.92/1.10  # Training examples: 0 positive, 0 negative
% 0.92/1.10  # Parsed axioms                        : 16
% 0.92/1.10  # Removed by relevancy pruning/SinE    : 0
% 0.92/1.10  # Initial clauses                      : 51
% 0.92/1.10  # Removed in clause preprocessing      : 1
% 0.92/1.10  # Initial clauses in saturation        : 50
% 0.92/1.10  # Processed clauses                    : 6975
% 0.92/1.10  # ...of these trivial                  : 89
% 0.92/1.10  # ...subsumed                          : 4436
% 0.92/1.10  # ...remaining for further processing  : 2450
% 0.92/1.10  # Other redundant clauses eliminated   : 5
% 0.92/1.10  # Clauses deleted for lack of memory   : 0
% 0.92/1.10  # Backward-subsumed                    : 221
% 0.92/1.10  # Backward-rewritten                   : 1861
% 0.92/1.10  # Generated clauses                    : 60577
% 0.92/1.10  # ...of the previous two non-trivial   : 60463
% 0.92/1.10  # Contextual simplify-reflections      : 29
% 0.92/1.10  # Paramodulations                      : 60549
% 0.92/1.10  # Factorizations                       : 4
% 0.92/1.10  # Equation resolutions                 : 6
% 0.92/1.10  # Propositional unsat checks           : 0
% 0.92/1.10  #    Propositional check models        : 0
% 0.92/1.10  #    Propositional check unsatisfiable : 0
% 0.92/1.10  #    Propositional clauses             : 0
% 0.92/1.10  #    Propositional clauses after purity: 0
% 0.92/1.10  #    Propositional unsat core size     : 0
% 0.92/1.10  #    Propositional preprocessing time  : 0.000
% 0.92/1.10  #    Propositional encoding time       : 0.000
% 0.92/1.10  #    Propositional solver time         : 0.000
% 0.92/1.10  #    Success case prop preproc time    : 0.000
% 0.92/1.10  #    Success case prop encoding time   : 0.000
% 0.92/1.10  #    Success case prop solver time     : 0.000
% 0.92/1.10  # Current number of processed clauses  : 295
% 0.92/1.10  #    Positive orientable unit clauses  : 49
% 0.92/1.10  #    Positive unorientable unit clauses: 1
% 0.92/1.10  #    Negative unit clauses             : 2
% 0.92/1.10  #    Non-unit-clauses                  : 243
% 0.92/1.10  # Current number of unprocessed clauses: 52368
% 0.92/1.10  # ...number of literals in the above   : 187358
% 0.92/1.10  # Current number of archived formulas  : 0
% 0.92/1.10  # Current number of archived clauses   : 2150
% 0.92/1.10  # Clause-clause subsumption calls (NU) : 351024
% 0.92/1.10  # Rec. Clause-clause subsumption calls : 233036
% 0.92/1.10  # Non-unit clause-clause subsumptions  : 4626
% 0.92/1.10  # Unit Clause-clause subsumption calls : 2935
% 0.92/1.10  # Rewrite failures with RHS unbound    : 0
% 0.92/1.10  # BW rewrite match attempts            : 320
% 0.92/1.10  # BW rewrite match successes           : 35
% 0.92/1.10  # Condensation attempts                : 0
% 0.92/1.10  # Condensation successes               : 0
% 0.92/1.10  # Termbank termtop insertions          : 1697008
% 0.92/1.11  
% 0.92/1.11  # -------------------------------------------------
% 0.92/1.11  # User time                : 0.734 s
% 0.92/1.11  # System time              : 0.034 s
% 0.92/1.11  # Total time               : 0.767 s
% 0.92/1.11  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
