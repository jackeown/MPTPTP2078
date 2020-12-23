%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:08 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 168 expanded)
%              Number of clauses        :   36 (  66 expanded)
%              Number of leaves         :   13 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :  462 (1265 expanded)
%              Number of equality atoms :   48 ( 106 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   50 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

fof(c_0_13,plain,(
    ! [X29,X30,X31,X32] :
      ( ( r4_lattice3(X29,X31,X30)
        | X31 != k15_lattice3(X29,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29)
        | v2_struct_0(X29)
        | ~ l3_lattices(X29) )
      & ( ~ m1_subset_1(X32,u1_struct_0(X29))
        | ~ r4_lattice3(X29,X32,X30)
        | r1_lattices(X29,X31,X32)
        | X31 != k15_lattice3(X29,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29)
        | v2_struct_0(X29)
        | ~ l3_lattices(X29) )
      & ( m1_subset_1(esk5_3(X29,X30,X31),u1_struct_0(X29))
        | ~ r4_lattice3(X29,X31,X30)
        | X31 = k15_lattice3(X29,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29)
        | v2_struct_0(X29)
        | ~ l3_lattices(X29) )
      & ( r4_lattice3(X29,esk5_3(X29,X30,X31),X30)
        | ~ r4_lattice3(X29,X31,X30)
        | X31 = k15_lattice3(X29,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29)
        | v2_struct_0(X29)
        | ~ l3_lattices(X29) )
      & ( ~ r1_lattices(X29,X31,esk5_3(X29,X30,X31))
        | ~ r4_lattice3(X29,X31,X30)
        | X31 = k15_lattice3(X29,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v10_lattices(X29)
        | ~ v4_lattice3(X29)
        | ~ l3_lattices(X29)
        | v2_struct_0(X29)
        | ~ l3_lattices(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

cnf(c_0_14,plain,
    ( r1_lattices(X2,X4,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r4_lattice3(X2,X1,X3)
    | X4 != k15_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_15,plain,(
    ! [X39,X40] :
      ( v2_struct_0(X39)
      | ~ l3_lattices(X39)
      | m1_subset_1(k15_lattice3(X39,X40),u1_struct_0(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_16,plain,(
    ! [X9,X10,X11] :
      ( ( k2_lattices(X9,X10,X11) = X10
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | X10 != k5_lattices(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ v13_lattices(X9)
        | v2_struct_0(X9)
        | ~ l1_lattices(X9) )
      & ( k2_lattices(X9,X11,X10) = X10
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | X10 != k5_lattices(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ v13_lattices(X9)
        | v2_struct_0(X9)
        | ~ l1_lattices(X9) )
      & ( m1_subset_1(esk1_2(X9,X10),u1_struct_0(X9))
        | X10 = k5_lattices(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ v13_lattices(X9)
        | v2_struct_0(X9)
        | ~ l1_lattices(X9) )
      & ( k2_lattices(X9,X10,esk1_2(X9,X10)) != X10
        | k2_lattices(X9,esk1_2(X9,X10),X10) != X10
        | X10 = k5_lattices(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ v13_lattices(X9)
        | v2_struct_0(X9)
        | ~ l1_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

fof(c_0_17,plain,(
    ! [X13] :
      ( v2_struct_0(X13)
      | ~ l1_lattices(X13)
      | m1_subset_1(k5_lattices(X13),u1_struct_0(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_18,plain,(
    ! [X15,X16,X17] :
      ( ( ~ r1_lattices(X15,X16,X17)
        | k2_lattices(X15,X16,X17) = X16
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v8_lattices(X15)
        | ~ v9_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( k2_lattices(X15,X16,X17) != X16
        | r1_lattices(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v8_lattices(X15)
        | ~ v9_lattices(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_19,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X8] :
      ( ( ~ v2_struct_0(X8)
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ l3_lattices(X8) )
      & ( v4_lattices(X8)
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ l3_lattices(X8) )
      & ( v5_lattices(X8)
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ l3_lattices(X8) )
      & ( v6_lattices(X8)
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ l3_lattices(X8) )
      & ( v7_lattices(X8)
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ l3_lattices(X8) )
      & ( v8_lattices(X8)
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ l3_lattices(X8) )
      & ( v9_lattices(X8)
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ l3_lattices(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_22,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | ~ r1_tarski(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_23,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ( ~ r4_lattice3(X23,X24,X25)
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ r2_hidden(X26,X25)
        | r1_lattices(X23,X26,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l3_lattices(X23) )
      & ( m1_subset_1(esk4_3(X23,X24,X27),u1_struct_0(X23))
        | r4_lattice3(X23,X24,X27)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l3_lattices(X23) )
      & ( r2_hidden(esk4_3(X23,X24,X27),X27)
        | r4_lattice3(X23,X24,X27)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l3_lattices(X23) )
      & ( ~ r1_lattices(X23,esk4_3(X23,X24,X27),X24)
        | r4_lattice3(X23,X24,X27)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l3_lattices(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

cnf(c_0_24,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( r1_lattices(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_20])).

cnf(c_0_28,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X14] :
      ( ( l1_lattices(X14)
        | ~ l3_lattices(X14) )
      & ( l2_lattices(X14)
        | ~ l3_lattices(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_34,plain,(
    ! [X18,X20,X21] :
      ( ( m1_subset_1(esk2_1(X18),u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) )
      & ( k2_lattices(X18,esk2_1(X18),X20) = esk2_1(X18)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) )
      & ( k2_lattices(X18,X20,esk2_1(X18)) = esk2_1(X18)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) )
      & ( m1_subset_1(esk3_2(X18,X21),u1_struct_0(X18))
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) )
      & ( k2_lattices(X18,X21,esk3_2(X18,X21)) != X21
        | k2_lattices(X18,esk3_2(X18,X21),X21) != X21
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

fof(c_0_35,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v6_lattices(X34)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | ~ m1_subset_1(X36,u1_struct_0(X34))
        | k2_lattices(X34,X35,X36) = k2_lattices(X34,X36,X35)
        | v2_struct_0(X34)
        | ~ l1_lattices(X34) )
      & ( m1_subset_1(esk6_1(X34),u1_struct_0(X34))
        | v6_lattices(X34)
        | v2_struct_0(X34)
        | ~ l1_lattices(X34) )
      & ( m1_subset_1(esk7_1(X34),u1_struct_0(X34))
        | v6_lattices(X34)
        | v2_struct_0(X34)
        | ~ l1_lattices(X34) )
      & ( k2_lattices(X34,esk6_1(X34),esk7_1(X34)) != k2_lattices(X34,esk7_1(X34),esk6_1(X34))
        | v6_lattices(X34)
        | v2_struct_0(X34)
        | ~ l1_lattices(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

fof(c_0_36,negated_conjecture,(
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

cnf(c_0_37,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]),c_0_25])).

cnf(c_0_38,plain,
    ( k2_lattices(X1,k15_lattice3(X1,X2),X3) = k15_lattice3(X1,X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_20])).

cnf(c_0_39,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ r1_tarski(X3,esk4_3(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | k2_lattices(X1,esk3_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    & v10_lattices(esk8_0)
    & v4_lattice3(esk8_0)
    & l3_lattices(esk8_0)
    & ( v2_struct_0(esk8_0)
      | ~ v10_lattices(esk8_0)
      | ~ v13_lattices(esk8_0)
      | ~ l3_lattices(esk8_0)
      | k5_lattices(esk8_0) != k15_lattice3(esk8_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_36])])])])).

cnf(c_0_46,plain,
    ( k15_lattice3(X1,X2) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,k5_lattices(X1),X2)
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_20])).

cnf(c_0_47,plain,
    ( r4_lattice3(X1,X2,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_49,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_50,negated_conjecture,
    ( v2_struct_0(esk8_0)
    | ~ v10_lattices(esk8_0)
    | ~ v13_lattices(esk8_0)
    | ~ l3_lattices(esk8_0)
    | k5_lattices(esk8_0) != k15_lattice3(esk8_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( l3_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( v10_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( k15_lattice3(X1,k1_xboole_0) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,esk3_2(X1,k15_lattice3(X1,X2)),X2)
    | ~ m1_subset_1(esk3_2(X1,k15_lattice3(X1,X2)),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_38]),c_0_49]),c_0_39]),c_0_20])).

cnf(c_0_56,negated_conjecture,
    ( k15_lattice3(esk8_0,k1_xboole_0) != k5_lattices(esk8_0)
    | ~ v13_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_52])]),c_0_53])).

cnf(c_0_57,plain,
    ( k15_lattice3(X1,k1_xboole_0) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v13_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_25]),c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( v4_lattice3(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_59,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk3_2(X1,k15_lattice3(X1,k1_xboole_0)),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_47])).

cnf(c_0_60,negated_conjecture,
    ( ~ v13_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_52]),c_0_51])]),c_0_53])).

cnf(c_0_61,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_44]),c_0_39]),c_0_20])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_58]),c_0_52]),c_0_51])]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:38:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.18/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.030 s
% 0.18/0.39  
% 0.18/0.39  # Proof found!
% 0.18/0.39  # SZS status Theorem
% 0.18/0.39  # SZS output start CNFRefutation
% 0.18/0.39  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 0.18/0.39  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.18/0.39  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 0.18/0.39  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.18/0.39  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 0.18/0.39  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.18/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.18/0.39  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 0.18/0.39  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.18/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.18/0.39  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 0.18/0.39  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 0.18/0.39  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 0.18/0.39  fof(c_0_13, plain, ![X29, X30, X31, X32]:(((r4_lattice3(X29,X31,X30)|X31!=k15_lattice3(X29,X30)|~m1_subset_1(X31,u1_struct_0(X29))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29))|(v2_struct_0(X29)|~l3_lattices(X29)))&(~m1_subset_1(X32,u1_struct_0(X29))|(~r4_lattice3(X29,X32,X30)|r1_lattices(X29,X31,X32))|X31!=k15_lattice3(X29,X30)|~m1_subset_1(X31,u1_struct_0(X29))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29))|(v2_struct_0(X29)|~l3_lattices(X29))))&((m1_subset_1(esk5_3(X29,X30,X31),u1_struct_0(X29))|~r4_lattice3(X29,X31,X30)|X31=k15_lattice3(X29,X30)|~m1_subset_1(X31,u1_struct_0(X29))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29))|(v2_struct_0(X29)|~l3_lattices(X29)))&((r4_lattice3(X29,esk5_3(X29,X30,X31),X30)|~r4_lattice3(X29,X31,X30)|X31=k15_lattice3(X29,X30)|~m1_subset_1(X31,u1_struct_0(X29))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29))|(v2_struct_0(X29)|~l3_lattices(X29)))&(~r1_lattices(X29,X31,esk5_3(X29,X30,X31))|~r4_lattice3(X29,X31,X30)|X31=k15_lattice3(X29,X30)|~m1_subset_1(X31,u1_struct_0(X29))|(v2_struct_0(X29)|~v10_lattices(X29)|~v4_lattice3(X29)|~l3_lattices(X29))|(v2_struct_0(X29)|~l3_lattices(X29)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.18/0.39  cnf(c_0_14, plain, (r1_lattices(X2,X4,X1)|v2_struct_0(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r4_lattice3(X2,X1,X3)|X4!=k15_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.39  fof(c_0_15, plain, ![X39, X40]:(v2_struct_0(X39)|~l3_lattices(X39)|m1_subset_1(k15_lattice3(X39,X40),u1_struct_0(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.18/0.39  fof(c_0_16, plain, ![X9, X10, X11]:(((k2_lattices(X9,X10,X11)=X10|~m1_subset_1(X11,u1_struct_0(X9))|X10!=k5_lattices(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~v13_lattices(X9)|(v2_struct_0(X9)|~l1_lattices(X9)))&(k2_lattices(X9,X11,X10)=X10|~m1_subset_1(X11,u1_struct_0(X9))|X10!=k5_lattices(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~v13_lattices(X9)|(v2_struct_0(X9)|~l1_lattices(X9))))&((m1_subset_1(esk1_2(X9,X10),u1_struct_0(X9))|X10=k5_lattices(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~v13_lattices(X9)|(v2_struct_0(X9)|~l1_lattices(X9)))&(k2_lattices(X9,X10,esk1_2(X9,X10))!=X10|k2_lattices(X9,esk1_2(X9,X10),X10)!=X10|X10=k5_lattices(X9)|~m1_subset_1(X10,u1_struct_0(X9))|~v13_lattices(X9)|(v2_struct_0(X9)|~l1_lattices(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.18/0.39  fof(c_0_17, plain, ![X13]:(v2_struct_0(X13)|~l1_lattices(X13)|m1_subset_1(k5_lattices(X13),u1_struct_0(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.18/0.39  fof(c_0_18, plain, ![X15, X16, X17]:((~r1_lattices(X15,X16,X17)|k2_lattices(X15,X16,X17)=X16|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~v8_lattices(X15)|~v9_lattices(X15)|~l3_lattices(X15)))&(k2_lattices(X15,X16,X17)!=X16|r1_lattices(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~v8_lattices(X15)|~v9_lattices(X15)|~l3_lattices(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.18/0.39  cnf(c_0_19, plain, (v2_struct_0(X2)|r1_lattices(X2,X4,X1)|X4!=k15_lattice3(X2,X3)|~l3_lattices(X2)|~v10_lattices(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))), inference(cn,[status(thm)],[c_0_14])).
% 0.18/0.39  cnf(c_0_20, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.39  fof(c_0_21, plain, ![X8]:(((((((~v2_struct_0(X8)|(v2_struct_0(X8)|~v10_lattices(X8))|~l3_lattices(X8))&(v4_lattices(X8)|(v2_struct_0(X8)|~v10_lattices(X8))|~l3_lattices(X8)))&(v5_lattices(X8)|(v2_struct_0(X8)|~v10_lattices(X8))|~l3_lattices(X8)))&(v6_lattices(X8)|(v2_struct_0(X8)|~v10_lattices(X8))|~l3_lattices(X8)))&(v7_lattices(X8)|(v2_struct_0(X8)|~v10_lattices(X8))|~l3_lattices(X8)))&(v8_lattices(X8)|(v2_struct_0(X8)|~v10_lattices(X8))|~l3_lattices(X8)))&(v9_lattices(X8)|(v2_struct_0(X8)|~v10_lattices(X8))|~l3_lattices(X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.18/0.39  fof(c_0_22, plain, ![X6, X7]:(~r2_hidden(X6,X7)|~r1_tarski(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.18/0.39  fof(c_0_23, plain, ![X23, X24, X25, X26, X27]:((~r4_lattice3(X23,X24,X25)|(~m1_subset_1(X26,u1_struct_0(X23))|(~r2_hidden(X26,X25)|r1_lattices(X23,X26,X24)))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~l3_lattices(X23)))&((m1_subset_1(esk4_3(X23,X24,X27),u1_struct_0(X23))|r4_lattice3(X23,X24,X27)|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~l3_lattices(X23)))&((r2_hidden(esk4_3(X23,X24,X27),X27)|r4_lattice3(X23,X24,X27)|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~l3_lattices(X23)))&(~r1_lattices(X23,esk4_3(X23,X24,X27),X24)|r4_lattice3(X23,X24,X27)|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~l3_lattices(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.18/0.39  cnf(c_0_24, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.39  cnf(c_0_25, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.39  cnf(c_0_26, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.39  cnf(c_0_27, plain, (r1_lattices(X1,k15_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]), c_0_20])).
% 0.18/0.39  cnf(c_0_28, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.39  cnf(c_0_29, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.39  fof(c_0_30, plain, ![X14]:((l1_lattices(X14)|~l3_lattices(X14))&(l2_lattices(X14)|~l3_lattices(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.18/0.39  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.39  cnf(c_0_32, plain, (r2_hidden(esk4_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.39  fof(c_0_33, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.18/0.39  fof(c_0_34, plain, ![X18, X20, X21]:(((m1_subset_1(esk2_1(X18),u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18)))&((k2_lattices(X18,esk2_1(X18),X20)=esk2_1(X18)|~m1_subset_1(X20,u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18)))&(k2_lattices(X18,X20,esk2_1(X18))=esk2_1(X18)|~m1_subset_1(X20,u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18)))))&((m1_subset_1(esk3_2(X18,X21),u1_struct_0(X18))|~m1_subset_1(X21,u1_struct_0(X18))|v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18)))&(k2_lattices(X18,X21,esk3_2(X18,X21))!=X21|k2_lattices(X18,esk3_2(X18,X21),X21)!=X21|~m1_subset_1(X21,u1_struct_0(X18))|v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 0.18/0.39  fof(c_0_35, plain, ![X34, X35, X36]:((~v6_lattices(X34)|(~m1_subset_1(X35,u1_struct_0(X34))|(~m1_subset_1(X36,u1_struct_0(X34))|k2_lattices(X34,X35,X36)=k2_lattices(X34,X36,X35)))|(v2_struct_0(X34)|~l1_lattices(X34)))&((m1_subset_1(esk6_1(X34),u1_struct_0(X34))|v6_lattices(X34)|(v2_struct_0(X34)|~l1_lattices(X34)))&((m1_subset_1(esk7_1(X34),u1_struct_0(X34))|v6_lattices(X34)|(v2_struct_0(X34)|~l1_lattices(X34)))&(k2_lattices(X34,esk6_1(X34),esk7_1(X34))!=k2_lattices(X34,esk7_1(X34),esk6_1(X34))|v6_lattices(X34)|(v2_struct_0(X34)|~l1_lattices(X34)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 0.18/0.39  fof(c_0_36, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 0.18/0.39  cnf(c_0_37, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]), c_0_25])).
% 0.18/0.39  cnf(c_0_38, plain, (k2_lattices(X1,k15_lattice3(X1,X2),X3)=k15_lattice3(X1,X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_20])).
% 0.18/0.39  cnf(c_0_39, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.39  cnf(c_0_40, plain, (r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)|~r1_tarski(X3,esk4_3(X1,X2,X3))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.18/0.39  cnf(c_0_41, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.39  cnf(c_0_42, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|k2_lattices(X1,esk3_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_43, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.39  cnf(c_0_44, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  fof(c_0_45, negated_conjecture, ((((~v2_struct_0(esk8_0)&v10_lattices(esk8_0))&v4_lattice3(esk8_0))&l3_lattices(esk8_0))&(v2_struct_0(esk8_0)|~v10_lattices(esk8_0)|~v13_lattices(esk8_0)|~l3_lattices(esk8_0)|k5_lattices(esk8_0)!=k15_lattice3(esk8_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_36])])])])).
% 0.18/0.39  cnf(c_0_46, plain, (k15_lattice3(X1,X2)=k5_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,k5_lattices(X1),X2)|~m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~v13_lattices(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_20])).
% 0.18/0.39  cnf(c_0_47, plain, (r4_lattice3(X1,X2,k1_xboole_0)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.39  cnf(c_0_48, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)|~v6_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.18/0.39  cnf(c_0_49, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.39  cnf(c_0_50, negated_conjecture, (v2_struct_0(esk8_0)|~v10_lattices(esk8_0)|~v13_lattices(esk8_0)|~l3_lattices(esk8_0)|k5_lattices(esk8_0)!=k15_lattice3(esk8_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.39  cnf(c_0_51, negated_conjecture, (l3_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.39  cnf(c_0_52, negated_conjecture, (v10_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.39  cnf(c_0_53, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.39  cnf(c_0_54, plain, (k15_lattice3(X1,k1_xboole_0)=k5_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~v13_lattices(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.18/0.39  cnf(c_0_55, plain, (v13_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,esk3_2(X1,k15_lattice3(X1,X2)),X2)|~m1_subset_1(esk3_2(X1,k15_lattice3(X1,X2)),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_38]), c_0_49]), c_0_39]), c_0_20])).
% 0.18/0.39  cnf(c_0_56, negated_conjecture, (k15_lattice3(esk8_0,k1_xboole_0)!=k5_lattices(esk8_0)|~v13_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_52])]), c_0_53])).
% 0.18/0.39  cnf(c_0_57, plain, (k15_lattice3(X1,k1_xboole_0)=k5_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~v13_lattices(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_25]), c_0_39])).
% 0.18/0.39  cnf(c_0_58, negated_conjecture, (v4_lattice3(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.39  cnf(c_0_59, plain, (v13_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk3_2(X1,k15_lattice3(X1,k1_xboole_0)),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_55, c_0_47])).
% 0.18/0.39  cnf(c_0_60, negated_conjecture, (~v13_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_52]), c_0_51])]), c_0_53])).
% 0.18/0.39  cnf(c_0_61, plain, (v13_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_44]), c_0_39]), c_0_20])).
% 0.18/0.39  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_58]), c_0_52]), c_0_51])]), c_0_53]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 63
% 0.18/0.39  # Proof object clause steps            : 36
% 0.18/0.39  # Proof object formula steps           : 27
% 0.18/0.39  # Proof object conjectures             : 11
% 0.18/0.39  # Proof object clause conjectures      : 8
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 20
% 0.18/0.39  # Proof object initial formulas used   : 13
% 0.18/0.39  # Proof object generating inferences   : 12
% 0.18/0.39  # Proof object simplifying inferences  : 31
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 13
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 42
% 0.18/0.39  # Removed in clause preprocessing      : 1
% 0.18/0.39  # Initial clauses in saturation        : 41
% 0.18/0.39  # Processed clauses                    : 214
% 0.18/0.39  # ...of these trivial                  : 0
% 0.18/0.39  # ...subsumed                          : 83
% 0.18/0.39  # ...remaining for further processing  : 131
% 0.18/0.39  # Other redundant clauses eliminated   : 4
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 17
% 0.18/0.39  # Backward-rewritten                   : 0
% 0.18/0.39  # Generated clauses                    : 239
% 0.18/0.39  # ...of the previous two non-trivial   : 205
% 0.18/0.39  # Contextual simplify-reflections      : 78
% 0.18/0.39  # Paramodulations                      : 235
% 0.18/0.39  # Factorizations                       : 0
% 0.18/0.39  # Equation resolutions                 : 4
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 110
% 0.18/0.39  #    Positive orientable unit clauses  : 4
% 0.18/0.39  #    Positive unorientable unit clauses: 0
% 0.18/0.39  #    Negative unit clauses             : 2
% 0.18/0.39  #    Non-unit-clauses                  : 104
% 0.18/0.39  # Current number of unprocessed clauses: 31
% 0.18/0.39  # ...number of literals in the above   : 346
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 17
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 8038
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 293
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 177
% 0.18/0.39  # Unit Clause-clause subsumption calls : 1
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 0
% 0.18/0.39  # BW rewrite match successes           : 0
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 12753
% 0.18/0.39  
% 0.18/0.39  # -------------------------------------------------
% 0.18/0.39  # User time                : 0.051 s
% 0.18/0.39  # System time              : 0.005 s
% 0.18/0.39  # Total time               : 0.056 s
% 0.18/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
