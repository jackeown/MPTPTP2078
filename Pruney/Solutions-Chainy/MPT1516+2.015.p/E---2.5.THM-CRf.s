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

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 (1261 expanded)
%              Number of clauses        :   63 ( 463 expanded)
%              Number of leaves         :   15 ( 306 expanded)
%              Depth                    :   14
%              Number of atoms          :  537 (7912 expanded)
%              Number of equality atoms :   81 ( 862 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

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
    ! [X23] :
      ( v2_struct_0(X23)
      | ~ l1_lattices(X23)
      | m1_subset_1(k5_lattices(X23),u1_struct_0(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_17,plain,(
    ! [X24] :
      ( ( l1_lattices(X24)
        | ~ l3_lattices(X24) )
      & ( l2_lattices(X24)
        | ~ l3_lattices(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_18,plain,(
    ! [X46,X47] :
      ( v2_struct_0(X46)
      | ~ l3_lattices(X46)
      | m1_subset_1(k15_lattice3(X46,X47),u1_struct_0(X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk12_0)
    & v10_lattices(esk12_0)
    & v4_lattice3(esk12_0)
    & l3_lattices(esk12_0)
    & ( v2_struct_0(esk12_0)
      | ~ v10_lattices(esk12_0)
      | ~ v13_lattices(esk12_0)
      | ~ l3_lattices(esk12_0)
      | k5_lattices(esk12_0) != k15_lattice3(esk12_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X10] :
      ( ( ~ v2_struct_0(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v4_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v5_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v6_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v7_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v8_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v9_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_23,plain,(
    ! [X36,X37,X38,X39] :
      ( ( r4_lattice3(X36,X38,X37)
        | X38 != k15_lattice3(X36,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v10_lattices(X36)
        | ~ v4_lattice3(X36)
        | ~ l3_lattices(X36)
        | v2_struct_0(X36)
        | ~ l3_lattices(X36) )
      & ( ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ r4_lattice3(X36,X39,X37)
        | r1_lattices(X36,X38,X39)
        | X38 != k15_lattice3(X36,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v10_lattices(X36)
        | ~ v4_lattice3(X36)
        | ~ l3_lattices(X36)
        | v2_struct_0(X36)
        | ~ l3_lattices(X36) )
      & ( m1_subset_1(esk7_3(X36,X37,X38),u1_struct_0(X36))
        | ~ r4_lattice3(X36,X38,X37)
        | X38 = k15_lattice3(X36,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v10_lattices(X36)
        | ~ v4_lattice3(X36)
        | ~ l3_lattices(X36)
        | v2_struct_0(X36)
        | ~ l3_lattices(X36) )
      & ( r4_lattice3(X36,esk7_3(X36,X37,X38),X37)
        | ~ r4_lattice3(X36,X38,X37)
        | X38 = k15_lattice3(X36,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v10_lattices(X36)
        | ~ v4_lattice3(X36)
        | ~ l3_lattices(X36)
        | v2_struct_0(X36)
        | ~ l3_lattices(X36) )
      & ( ~ r1_lattices(X36,X38,esk7_3(X36,X37,X38))
        | ~ r4_lattice3(X36,X38,X37)
        | X38 = k15_lattice3(X36,X37)
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v10_lattices(X36)
        | ~ v4_lattice3(X36)
        | ~ l3_lattices(X36)
        | v2_struct_0(X36)
        | ~ l3_lattices(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

fof(c_0_24,plain,(
    ! [X25,X27,X28] :
      ( ( m1_subset_1(esk4_1(X25),u1_struct_0(X25))
        | ~ v13_lattices(X25)
        | v2_struct_0(X25)
        | ~ l1_lattices(X25) )
      & ( k2_lattices(X25,esk4_1(X25),X27) = esk4_1(X25)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ v13_lattices(X25)
        | v2_struct_0(X25)
        | ~ l1_lattices(X25) )
      & ( k2_lattices(X25,X27,esk4_1(X25)) = esk4_1(X25)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ v13_lattices(X25)
        | v2_struct_0(X25)
        | ~ l1_lattices(X25) )
      & ( m1_subset_1(esk5_2(X25,X28),u1_struct_0(X25))
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | v13_lattices(X25)
        | v2_struct_0(X25)
        | ~ l1_lattices(X25) )
      & ( k2_lattices(X25,X28,esk5_2(X25,X28)) != X28
        | k2_lattices(X25,esk5_2(X25,X28),X28) != X28
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | v13_lattices(X25)
        | v2_struct_0(X25)
        | ~ l1_lattices(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( l3_lattices(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_29,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v9_lattices(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | k2_lattices(X18,X19,k1_lattices(X18,X19,X20)) = X19
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( m1_subset_1(esk2_1(X18),u1_struct_0(X18))
        | v9_lattices(X18)
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( m1_subset_1(esk3_1(X18),u1_struct_0(X18))
        | v9_lattices(X18)
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) )
      & ( k2_lattices(X18,esk2_1(X18),k1_lattices(X18,esk2_1(X18),esk3_1(X18))) != esk2_1(X18)
        | v9_lattices(X18)
        | v2_struct_0(X18)
        | ~ l3_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).

cnf(c_0_30,plain,
    ( m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( v10_lattices(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_33,plain,(
    ! [X15,X16,X17] :
      ( ( ~ r1_lattices(X15,X16,X17)
        | k1_lattices(X15,X16,X17) = X17
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l2_lattices(X15) )
      & ( k1_lattices(X15,X16,X17) != X17
        | r1_lattices(X15,X16,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l2_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

cnf(c_0_34,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk12_0,X1),u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

fof(c_0_37,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_39,plain,(
    ! [X30,X31,X32,X33,X34] :
      ( ( ~ r4_lattice3(X30,X31,X32)
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ r2_hidden(X33,X32)
        | r1_lattices(X30,X33,X31)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ l3_lattices(X30) )
      & ( m1_subset_1(esk6_3(X30,X31,X34),u1_struct_0(X30))
        | r4_lattice3(X30,X31,X34)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ l3_lattices(X30) )
      & ( r2_hidden(esk6_3(X30,X31,X34),X34)
        | r4_lattice3(X30,X31,X34)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ l3_lattices(X30) )
      & ( ~ r1_lattices(X30,esk6_3(X30,X31,X34),X31)
        | r4_lattice3(X30,X31,X34)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ l3_lattices(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

fof(c_0_40,plain,(
    ! [X11,X12,X13] :
      ( ( k2_lattices(X11,X12,X13) = X12
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | X12 != k5_lattices(X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ v13_lattices(X11)
        | v2_struct_0(X11)
        | ~ l1_lattices(X11) )
      & ( k2_lattices(X11,X13,X12) = X12
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | X12 != k5_lattices(X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ v13_lattices(X11)
        | v2_struct_0(X11)
        | ~ l1_lattices(X11) )
      & ( m1_subset_1(esk1_2(X11,X12),u1_struct_0(X11))
        | X12 = k5_lattices(X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ v13_lattices(X11)
        | v2_struct_0(X11)
        | ~ l1_lattices(X11) )
      & ( k2_lattices(X11,X12,esk1_2(X11,X12)) != X12
        | k2_lattices(X11,esk1_2(X11,X12),X12) != X12
        | X12 = k5_lattices(X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ v13_lattices(X11)
        | v2_struct_0(X11)
        | ~ l1_lattices(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

cnf(c_0_41,plain,
    ( k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk12_0),u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( v9_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_26])]),c_0_27])).

cnf(c_0_44,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_34])).

fof(c_0_46,plain,(
    ! [X53,X54] :
      ( ( X54 = k15_lattice3(X53,a_2_3_lattice3(X53,X54))
        | ~ m1_subset_1(X54,u1_struct_0(X53))
        | v2_struct_0(X53)
        | ~ v10_lattices(X53)
        | ~ v4_lattice3(X53)
        | ~ l3_lattices(X53) )
      & ( X54 = k16_lattice3(X53,a_2_4_lattice3(X53,X54))
        | ~ m1_subset_1(X54,u1_struct_0(X53))
        | v2_struct_0(X53)
        | ~ v10_lattices(X53)
        | ~ v4_lattice3(X53)
        | ~ l3_lattices(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk5_2(esk12_0,k15_lattice3(esk12_0,X1)),u1_struct_0(esk12_0))
    | v13_lattices(esk12_0)
    | ~ l1_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_27])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( k2_lattices(esk12_0,X1,k1_lattices(esk12_0,X1,k5_lattices(esk12_0))) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_26])]),c_0_27])).

cnf(c_0_53,negated_conjecture,
    ( k1_lattices(esk12_0,X1,k5_lattices(esk12_0)) = k5_lattices(esk12_0)
    | ~ r1_lattices(esk12_0,X1,k5_lattices(esk12_0))
    | ~ l2_lattices(esk12_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_42]),c_0_27])).

cnf(c_0_54,plain,
    ( r1_lattices(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]),c_0_25])).

cnf(c_0_55,negated_conjecture,
    ( v4_lattice3(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_56,negated_conjecture,
    ( k2_lattices(esk12_0,X1,k1_lattices(esk12_0,X1,k15_lattice3(esk12_0,X2))) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_36]),c_0_43]),c_0_26])]),c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( k1_lattices(esk12_0,X1,k15_lattice3(esk12_0,X2)) = k15_lattice3(esk12_0,X2)
    | ~ r1_lattices(esk12_0,X1,k15_lattice3(esk12_0,X2))
    | ~ l2_lattices(esk12_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_36]),c_0_27])).

cnf(c_0_58,plain,
    ( X1 = k15_lattice3(X2,a_2_3_lattice3(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk5_2(esk12_0,k15_lattice3(esk12_0,X1)),u1_struct_0(esk12_0))
    | v13_lattices(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_21]),c_0_26])])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( r4_lattice3(esk12_0,k15_lattice3(esk12_0,X1),X2)
    | r2_hidden(esk6_3(esk12_0,k15_lattice3(esk12_0,X1),X2),X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_36]),c_0_26])]),c_0_27])).

cnf(c_0_62,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_51]),c_0_20])).

cnf(c_0_63,negated_conjecture,
    ( k2_lattices(esk12_0,X1,k5_lattices(esk12_0)) = X1
    | ~ r1_lattices(esk12_0,X1,k5_lattices(esk12_0))
    | ~ l2_lattices(esk12_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( r1_lattices(esk12_0,k15_lattice3(esk12_0,X1),k5_lattices(esk12_0))
    | ~ r4_lattice3(esk12_0,k5_lattices(esk12_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_42]),c_0_55]),c_0_32]),c_0_26])]),c_0_27])).

cnf(c_0_65,negated_conjecture,
    ( k2_lattices(esk12_0,X1,k15_lattice3(esk12_0,X2)) = X1
    | ~ r1_lattices(esk12_0,X1,k15_lattice3(esk12_0,X2))
    | ~ l2_lattices(esk12_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( k15_lattice3(esk12_0,a_2_3_lattice3(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,X1)))) = esk5_2(esk12_0,k15_lattice3(esk12_0,X1))
    | v13_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_55]),c_0_32]),c_0_26])]),c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( r4_lattice3(esk12_0,k15_lattice3(esk12_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( k2_lattices(esk12_0,k15_lattice3(esk12_0,X1),k5_lattices(esk12_0)) = k5_lattices(esk12_0)
    | ~ v13_lattices(esk12_0)
    | ~ l1_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_36]),c_0_27])).

cnf(c_0_69,negated_conjecture,
    ( k2_lattices(esk12_0,k15_lattice3(esk12_0,X1),k5_lattices(esk12_0)) = k15_lattice3(esk12_0,X1)
    | ~ r4_lattice3(esk12_0,k5_lattices(esk12_0),X1)
    | ~ l2_lattices(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_36])])).

cnf(c_0_70,negated_conjecture,
    ( r4_lattice3(esk12_0,k5_lattices(esk12_0),X1)
    | r2_hidden(esk6_3(esk12_0,k5_lattices(esk12_0),X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_42]),c_0_26])]),c_0_27])).

cnf(c_0_71,negated_conjecture,
    ( v2_struct_0(esk12_0)
    | ~ v10_lattices(esk12_0)
    | ~ v13_lattices(esk12_0)
    | ~ l3_lattices(esk12_0)
    | k5_lattices(esk12_0) != k15_lattice3(esk12_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_72,negated_conjecture,
    ( k2_lattices(esk12_0,X1,esk5_2(esk12_0,k15_lattice3(esk12_0,X2))) = X1
    | v13_lattices(esk12_0)
    | ~ r1_lattices(esk12_0,X1,esk5_2(esk12_0,k15_lattice3(esk12_0,X2)))
    | ~ l2_lattices(esk12_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_74,negated_conjecture,
    ( r1_lattices(esk12_0,k15_lattice3(esk12_0,X1),esk5_2(esk12_0,k15_lattice3(esk12_0,X2)))
    | v13_lattices(esk12_0)
    | ~ r4_lattice3(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,X2)),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_59]),c_0_55]),c_0_32]),c_0_26])]),c_0_27])).

cnf(c_0_75,negated_conjecture,
    ( r4_lattice3(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,X1)),k1_xboole_0)
    | v13_lattices(esk12_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( k15_lattice3(esk12_0,X1) = k5_lattices(esk12_0)
    | ~ r4_lattice3(esk12_0,k5_lattices(esk12_0),X1)
    | ~ l2_lattices(esk12_0)
    | ~ v13_lattices(esk12_0)
    | ~ l1_lattices(esk12_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( r4_lattice3(esk12_0,k5_lattices(esk12_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( k5_lattices(esk12_0) != k15_lattice3(esk12_0,k1_xboole_0)
    | ~ v13_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_26]),c_0_32])]),c_0_27])).

cnf(c_0_79,negated_conjecture,
    ( k2_lattices(esk12_0,X1,esk5_2(esk12_0,k15_lattice3(esk12_0,X2))) = X1
    | v13_lattices(esk12_0)
    | ~ r1_lattices(esk12_0,X1,esk5_2(esk12_0,k15_lattice3(esk12_0,X2)))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_26])])).

cnf(c_0_80,negated_conjecture,
    ( r1_lattices(esk12_0,k15_lattice3(esk12_0,k1_xboole_0),esk5_2(esk12_0,k15_lattice3(esk12_0,X1)))
    | v13_lattices(esk12_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( ~ l2_lattices(esk12_0)
    | ~ v13_lattices(esk12_0)
    | ~ l1_lattices(esk12_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

fof(c_0_82,plain,(
    ! [X41,X42,X43] :
      ( ( ~ v6_lattices(X41)
        | ~ m1_subset_1(X42,u1_struct_0(X41))
        | ~ m1_subset_1(X43,u1_struct_0(X41))
        | k2_lattices(X41,X42,X43) = k2_lattices(X41,X43,X42)
        | v2_struct_0(X41)
        | ~ l1_lattices(X41) )
      & ( m1_subset_1(esk8_1(X41),u1_struct_0(X41))
        | v6_lattices(X41)
        | v2_struct_0(X41)
        | ~ l1_lattices(X41) )
      & ( m1_subset_1(esk9_1(X41),u1_struct_0(X41))
        | v6_lattices(X41)
        | v2_struct_0(X41)
        | ~ l1_lattices(X41) )
      & ( k2_lattices(X41,esk8_1(X41),esk9_1(X41)) != k2_lattices(X41,esk9_1(X41),esk8_1(X41))
        | v6_lattices(X41)
        | v2_struct_0(X41)
        | ~ l1_lattices(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

cnf(c_0_83,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_84,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk5_2(X1,X2)) != X2
    | k2_lattices(X1,esk5_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_85,negated_conjecture,
    ( k2_lattices(esk12_0,k15_lattice3(esk12_0,k1_xboole_0),esk5_2(esk12_0,k15_lattice3(esk12_0,X1))) = k15_lattice3(esk12_0,k1_xboole_0)
    | v13_lattices(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_36])])).

cnf(c_0_86,negated_conjecture,
    ( ~ v13_lattices(esk12_0)
    | ~ l1_lattices(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_73]),c_0_26])])).

cnf(c_0_87,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( v6_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_32]),c_0_26])]),c_0_27])).

cnf(c_0_89,negated_conjecture,
    ( k2_lattices(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,k1_xboole_0)),k15_lattice3(esk12_0,k1_xboole_0)) != k15_lattice3(esk12_0,k1_xboole_0)
    | ~ l1_lattices(esk12_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_36])]),c_0_27]),c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( k2_lattices(esk12_0,X1,esk5_2(esk12_0,k15_lattice3(esk12_0,X2))) = k2_lattices(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,X2)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0))
    | ~ l1_lattices(esk12_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_59]),c_0_88])]),c_0_27]),c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( k2_lattices(esk12_0,k15_lattice3(esk12_0,k1_xboole_0),esk5_2(esk12_0,k15_lattice3(esk12_0,k1_xboole_0))) != k15_lattice3(esk12_0,k1_xboole_0)
    | ~ l1_lattices(esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_36])])).

cnf(c_0_92,negated_conjecture,
    ( ~ l1_lattices(esk12_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_85]),c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_21]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.46  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.46  #
% 0.20/0.46  # Preprocessing time       : 0.031 s
% 0.20/0.46  # Presaturation interreduction done
% 0.20/0.46  
% 0.20/0.46  # Proof found!
% 0.20/0.46  # SZS status Theorem
% 0.20/0.46  # SZS output start CNFRefutation
% 0.20/0.46  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_lattice3)).
% 0.20/0.46  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.20/0.46  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.20/0.46  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.20/0.46  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.20/0.46  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 0.20/0.46  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_lattices)).
% 0.20/0.46  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.46  fof(d9_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v9_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattices)).
% 0.20/0.46  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 0.20/0.46  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.20/0.46  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 0.20/0.46  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 0.20/0.46  fof(t45_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k15_lattice3(X1,a_2_3_lattice3(X1,X2))&X2=k16_lattice3(X1,a_2_4_lattice3(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_lattice3)).
% 0.20/0.46  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_lattices)).
% 0.20/0.46  fof(c_0_15, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 0.20/0.46  fof(c_0_16, plain, ![X23]:(v2_struct_0(X23)|~l1_lattices(X23)|m1_subset_1(k5_lattices(X23),u1_struct_0(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.20/0.46  fof(c_0_17, plain, ![X24]:((l1_lattices(X24)|~l3_lattices(X24))&(l2_lattices(X24)|~l3_lattices(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.20/0.46  fof(c_0_18, plain, ![X46, X47]:(v2_struct_0(X46)|~l3_lattices(X46)|m1_subset_1(k15_lattice3(X46,X47),u1_struct_0(X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.20/0.46  fof(c_0_19, negated_conjecture, ((((~v2_struct_0(esk12_0)&v10_lattices(esk12_0))&v4_lattice3(esk12_0))&l3_lattices(esk12_0))&(v2_struct_0(esk12_0)|~v10_lattices(esk12_0)|~v13_lattices(esk12_0)|~l3_lattices(esk12_0)|k5_lattices(esk12_0)!=k15_lattice3(esk12_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.20/0.46  cnf(c_0_20, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.46  cnf(c_0_21, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.46  fof(c_0_22, plain, ![X10]:(((((((~v2_struct_0(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10))&(v4_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v5_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v6_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v7_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v8_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v9_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.20/0.46  fof(c_0_23, plain, ![X36, X37, X38, X39]:(((r4_lattice3(X36,X38,X37)|X38!=k15_lattice3(X36,X37)|~m1_subset_1(X38,u1_struct_0(X36))|(v2_struct_0(X36)|~v10_lattices(X36)|~v4_lattice3(X36)|~l3_lattices(X36))|(v2_struct_0(X36)|~l3_lattices(X36)))&(~m1_subset_1(X39,u1_struct_0(X36))|(~r4_lattice3(X36,X39,X37)|r1_lattices(X36,X38,X39))|X38!=k15_lattice3(X36,X37)|~m1_subset_1(X38,u1_struct_0(X36))|(v2_struct_0(X36)|~v10_lattices(X36)|~v4_lattice3(X36)|~l3_lattices(X36))|(v2_struct_0(X36)|~l3_lattices(X36))))&((m1_subset_1(esk7_3(X36,X37,X38),u1_struct_0(X36))|~r4_lattice3(X36,X38,X37)|X38=k15_lattice3(X36,X37)|~m1_subset_1(X38,u1_struct_0(X36))|(v2_struct_0(X36)|~v10_lattices(X36)|~v4_lattice3(X36)|~l3_lattices(X36))|(v2_struct_0(X36)|~l3_lattices(X36)))&((r4_lattice3(X36,esk7_3(X36,X37,X38),X37)|~r4_lattice3(X36,X38,X37)|X38=k15_lattice3(X36,X37)|~m1_subset_1(X38,u1_struct_0(X36))|(v2_struct_0(X36)|~v10_lattices(X36)|~v4_lattice3(X36)|~l3_lattices(X36))|(v2_struct_0(X36)|~l3_lattices(X36)))&(~r1_lattices(X36,X38,esk7_3(X36,X37,X38))|~r4_lattice3(X36,X38,X37)|X38=k15_lattice3(X36,X37)|~m1_subset_1(X38,u1_struct_0(X36))|(v2_struct_0(X36)|~v10_lattices(X36)|~v4_lattice3(X36)|~l3_lattices(X36))|(v2_struct_0(X36)|~l3_lattices(X36)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 0.20/0.46  fof(c_0_24, plain, ![X25, X27, X28]:(((m1_subset_1(esk4_1(X25),u1_struct_0(X25))|~v13_lattices(X25)|(v2_struct_0(X25)|~l1_lattices(X25)))&((k2_lattices(X25,esk4_1(X25),X27)=esk4_1(X25)|~m1_subset_1(X27,u1_struct_0(X25))|~v13_lattices(X25)|(v2_struct_0(X25)|~l1_lattices(X25)))&(k2_lattices(X25,X27,esk4_1(X25))=esk4_1(X25)|~m1_subset_1(X27,u1_struct_0(X25))|~v13_lattices(X25)|(v2_struct_0(X25)|~l1_lattices(X25)))))&((m1_subset_1(esk5_2(X25,X28),u1_struct_0(X25))|~m1_subset_1(X28,u1_struct_0(X25))|v13_lattices(X25)|(v2_struct_0(X25)|~l1_lattices(X25)))&(k2_lattices(X25,X28,esk5_2(X25,X28))!=X28|k2_lattices(X25,esk5_2(X25,X28),X28)!=X28|~m1_subset_1(X28,u1_struct_0(X25))|v13_lattices(X25)|(v2_struct_0(X25)|~l1_lattices(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 0.20/0.46  cnf(c_0_25, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.46  cnf(c_0_26, negated_conjecture, (l3_lattices(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  fof(c_0_28, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.46  fof(c_0_29, plain, ![X18, X19, X20]:((~v9_lattices(X18)|(~m1_subset_1(X19,u1_struct_0(X18))|(~m1_subset_1(X20,u1_struct_0(X18))|k2_lattices(X18,X19,k1_lattices(X18,X19,X20))=X19))|(v2_struct_0(X18)|~l3_lattices(X18)))&((m1_subset_1(esk2_1(X18),u1_struct_0(X18))|v9_lattices(X18)|(v2_struct_0(X18)|~l3_lattices(X18)))&((m1_subset_1(esk3_1(X18),u1_struct_0(X18))|v9_lattices(X18)|(v2_struct_0(X18)|~l3_lattices(X18)))&(k2_lattices(X18,esk2_1(X18),k1_lattices(X18,esk2_1(X18),esk3_1(X18)))!=esk2_1(X18)|v9_lattices(X18)|(v2_struct_0(X18)|~l3_lattices(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).
% 0.20/0.46  cnf(c_0_30, plain, (m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.46  cnf(c_0_31, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.46  cnf(c_0_32, negated_conjecture, (v10_lattices(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  fof(c_0_33, plain, ![X15, X16, X17]:((~r1_lattices(X15,X16,X17)|k1_lattices(X15,X16,X17)=X17|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l2_lattices(X15)))&(k1_lattices(X15,X16,X17)!=X17|r1_lattices(X15,X16,X17)|~m1_subset_1(X17,u1_struct_0(X15))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l2_lattices(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.20/0.46  cnf(c_0_34, plain, (r1_lattices(X2,X4,X1)|v2_struct_0(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r4_lattice3(X2,X1,X3)|X4!=k15_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_35, plain, (m1_subset_1(esk5_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.46  cnf(c_0_36, negated_conjecture, (m1_subset_1(k15_lattice3(esk12_0,X1),u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.20/0.46  fof(c_0_37, plain, ![X8, X9]:~r2_hidden(X8,k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.20/0.46  cnf(c_0_38, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.46  fof(c_0_39, plain, ![X30, X31, X32, X33, X34]:((~r4_lattice3(X30,X31,X32)|(~m1_subset_1(X33,u1_struct_0(X30))|(~r2_hidden(X33,X32)|r1_lattices(X30,X33,X31)))|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~l3_lattices(X30)))&((m1_subset_1(esk6_3(X30,X31,X34),u1_struct_0(X30))|r4_lattice3(X30,X31,X34)|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~l3_lattices(X30)))&((r2_hidden(esk6_3(X30,X31,X34),X34)|r4_lattice3(X30,X31,X34)|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~l3_lattices(X30)))&(~r1_lattices(X30,esk6_3(X30,X31,X34),X31)|r4_lattice3(X30,X31,X34)|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~l3_lattices(X30)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 0.20/0.46  fof(c_0_40, plain, ![X11, X12, X13]:(((k2_lattices(X11,X12,X13)=X12|~m1_subset_1(X13,u1_struct_0(X11))|X12!=k5_lattices(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~v13_lattices(X11)|(v2_struct_0(X11)|~l1_lattices(X11)))&(k2_lattices(X11,X13,X12)=X12|~m1_subset_1(X13,u1_struct_0(X11))|X12!=k5_lattices(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~v13_lattices(X11)|(v2_struct_0(X11)|~l1_lattices(X11))))&((m1_subset_1(esk1_2(X11,X12),u1_struct_0(X11))|X12=k5_lattices(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~v13_lattices(X11)|(v2_struct_0(X11)|~l1_lattices(X11)))&(k2_lattices(X11,X12,esk1_2(X11,X12))!=X12|k2_lattices(X11,esk1_2(X11,X12),X12)!=X12|X12=k5_lattices(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~v13_lattices(X11)|(v2_struct_0(X11)|~l1_lattices(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.20/0.46  cnf(c_0_41, plain, (k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2|v2_struct_0(X1)|~v9_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.46  cnf(c_0_42, negated_conjecture, (m1_subset_1(k5_lattices(esk12_0),u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_26]), c_0_27])).
% 0.20/0.46  cnf(c_0_43, negated_conjecture, (v9_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_26])]), c_0_27])).
% 0.20/0.46  cnf(c_0_44, plain, (k1_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.46  cnf(c_0_45, plain, (v2_struct_0(X2)|r1_lattices(X2,X4,X1)|X4!=k15_lattice3(X2,X3)|~l3_lattices(X2)|~v10_lattices(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))), inference(cn,[status(thm)],[c_0_34])).
% 0.20/0.46  fof(c_0_46, plain, ![X53, X54]:((X54=k15_lattice3(X53,a_2_3_lattice3(X53,X54))|~m1_subset_1(X54,u1_struct_0(X53))|(v2_struct_0(X53)|~v10_lattices(X53)|~v4_lattice3(X53)|~l3_lattices(X53)))&(X54=k16_lattice3(X53,a_2_4_lattice3(X53,X54))|~m1_subset_1(X54,u1_struct_0(X53))|(v2_struct_0(X53)|~v10_lattices(X53)|~v4_lattice3(X53)|~l3_lattices(X53)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).
% 0.20/0.46  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk5_2(esk12_0,k15_lattice3(esk12_0,X1)),u1_struct_0(esk12_0))|v13_lattices(esk12_0)|~l1_lattices(esk12_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_27])).
% 0.20/0.46  cnf(c_0_48, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.46  cnf(c_0_49, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_38])).
% 0.20/0.46  cnf(c_0_50, plain, (r2_hidden(esk6_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.46  cnf(c_0_51, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.46  cnf(c_0_52, negated_conjecture, (k2_lattices(esk12_0,X1,k1_lattices(esk12_0,X1,k5_lattices(esk12_0)))=X1|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_26])]), c_0_27])).
% 0.20/0.46  cnf(c_0_53, negated_conjecture, (k1_lattices(esk12_0,X1,k5_lattices(esk12_0))=k5_lattices(esk12_0)|~r1_lattices(esk12_0,X1,k5_lattices(esk12_0))|~l2_lattices(esk12_0)|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_42]), c_0_27])).
% 0.20/0.46  cnf(c_0_54, plain, (r1_lattices(X1,k15_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]), c_0_25])).
% 0.20/0.46  cnf(c_0_55, negated_conjecture, (v4_lattice3(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_56, negated_conjecture, (k2_lattices(esk12_0,X1,k1_lattices(esk12_0,X1,k15_lattice3(esk12_0,X2)))=X1|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_36]), c_0_43]), c_0_26])]), c_0_27])).
% 0.20/0.46  cnf(c_0_57, negated_conjecture, (k1_lattices(esk12_0,X1,k15_lattice3(esk12_0,X2))=k15_lattice3(esk12_0,X2)|~r1_lattices(esk12_0,X1,k15_lattice3(esk12_0,X2))|~l2_lattices(esk12_0)|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_36]), c_0_27])).
% 0.20/0.46  cnf(c_0_58, plain, (X1=k15_lattice3(X2,a_2_3_lattice3(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.46  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk5_2(esk12_0,k15_lattice3(esk12_0,X1)),u1_struct_0(esk12_0))|v13_lattices(esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_21]), c_0_26])])).
% 0.20/0.46  cnf(c_0_60, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.46  cnf(c_0_61, negated_conjecture, (r4_lattice3(esk12_0,k15_lattice3(esk12_0,X1),X2)|r2_hidden(esk6_3(esk12_0,k15_lattice3(esk12_0,X1),X2),X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_36]), c_0_26])]), c_0_27])).
% 0.20/0.46  cnf(c_0_62, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_51]), c_0_20])).
% 0.20/0.46  cnf(c_0_63, negated_conjecture, (k2_lattices(esk12_0,X1,k5_lattices(esk12_0))=X1|~r1_lattices(esk12_0,X1,k5_lattices(esk12_0))|~l2_lattices(esk12_0)|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.46  cnf(c_0_64, negated_conjecture, (r1_lattices(esk12_0,k15_lattice3(esk12_0,X1),k5_lattices(esk12_0))|~r4_lattice3(esk12_0,k5_lattices(esk12_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_42]), c_0_55]), c_0_32]), c_0_26])]), c_0_27])).
% 0.20/0.46  cnf(c_0_65, negated_conjecture, (k2_lattices(esk12_0,X1,k15_lattice3(esk12_0,X2))=X1|~r1_lattices(esk12_0,X1,k15_lattice3(esk12_0,X2))|~l2_lattices(esk12_0)|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.46  cnf(c_0_66, negated_conjecture, (k15_lattice3(esk12_0,a_2_3_lattice3(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,X1))))=esk5_2(esk12_0,k15_lattice3(esk12_0,X1))|v13_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_55]), c_0_32]), c_0_26])]), c_0_27])).
% 0.20/0.46  cnf(c_0_67, negated_conjecture, (r4_lattice3(esk12_0,k15_lattice3(esk12_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.46  cnf(c_0_68, negated_conjecture, (k2_lattices(esk12_0,k15_lattice3(esk12_0,X1),k5_lattices(esk12_0))=k5_lattices(esk12_0)|~v13_lattices(esk12_0)|~l1_lattices(esk12_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_36]), c_0_27])).
% 0.20/0.46  cnf(c_0_69, negated_conjecture, (k2_lattices(esk12_0,k15_lattice3(esk12_0,X1),k5_lattices(esk12_0))=k15_lattice3(esk12_0,X1)|~r4_lattice3(esk12_0,k5_lattices(esk12_0),X1)|~l2_lattices(esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_36])])).
% 0.20/0.46  cnf(c_0_70, negated_conjecture, (r4_lattice3(esk12_0,k5_lattices(esk12_0),X1)|r2_hidden(esk6_3(esk12_0,k5_lattices(esk12_0),X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_42]), c_0_26])]), c_0_27])).
% 0.20/0.46  cnf(c_0_71, negated_conjecture, (v2_struct_0(esk12_0)|~v10_lattices(esk12_0)|~v13_lattices(esk12_0)|~l3_lattices(esk12_0)|k5_lattices(esk12_0)!=k15_lattice3(esk12_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_72, negated_conjecture, (k2_lattices(esk12_0,X1,esk5_2(esk12_0,k15_lattice3(esk12_0,X2)))=X1|v13_lattices(esk12_0)|~r1_lattices(esk12_0,X1,esk5_2(esk12_0,k15_lattice3(esk12_0,X2)))|~l2_lattices(esk12_0)|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.46  cnf(c_0_73, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.46  cnf(c_0_74, negated_conjecture, (r1_lattices(esk12_0,k15_lattice3(esk12_0,X1),esk5_2(esk12_0,k15_lattice3(esk12_0,X2)))|v13_lattices(esk12_0)|~r4_lattice3(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,X2)),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_59]), c_0_55]), c_0_32]), c_0_26])]), c_0_27])).
% 0.20/0.46  cnf(c_0_75, negated_conjecture, (r4_lattice3(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,X1)),k1_xboole_0)|v13_lattices(esk12_0)), inference(spm,[status(thm)],[c_0_67, c_0_66])).
% 0.20/0.46  cnf(c_0_76, negated_conjecture, (k15_lattice3(esk12_0,X1)=k5_lattices(esk12_0)|~r4_lattice3(esk12_0,k5_lattices(esk12_0),X1)|~l2_lattices(esk12_0)|~v13_lattices(esk12_0)|~l1_lattices(esk12_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.46  cnf(c_0_77, negated_conjecture, (r4_lattice3(esk12_0,k5_lattices(esk12_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_70])).
% 0.20/0.46  cnf(c_0_78, negated_conjecture, (k5_lattices(esk12_0)!=k15_lattice3(esk12_0,k1_xboole_0)|~v13_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_26]), c_0_32])]), c_0_27])).
% 0.20/0.46  cnf(c_0_79, negated_conjecture, (k2_lattices(esk12_0,X1,esk5_2(esk12_0,k15_lattice3(esk12_0,X2)))=X1|v13_lattices(esk12_0)|~r1_lattices(esk12_0,X1,esk5_2(esk12_0,k15_lattice3(esk12_0,X2)))|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_26])])).
% 0.20/0.46  cnf(c_0_80, negated_conjecture, (r1_lattices(esk12_0,k15_lattice3(esk12_0,k1_xboole_0),esk5_2(esk12_0,k15_lattice3(esk12_0,X1)))|v13_lattices(esk12_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.46  cnf(c_0_81, negated_conjecture, (~l2_lattices(esk12_0)|~v13_lattices(esk12_0)|~l1_lattices(esk12_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])).
% 0.20/0.46  fof(c_0_82, plain, ![X41, X42, X43]:((~v6_lattices(X41)|(~m1_subset_1(X42,u1_struct_0(X41))|(~m1_subset_1(X43,u1_struct_0(X41))|k2_lattices(X41,X42,X43)=k2_lattices(X41,X43,X42)))|(v2_struct_0(X41)|~l1_lattices(X41)))&((m1_subset_1(esk8_1(X41),u1_struct_0(X41))|v6_lattices(X41)|(v2_struct_0(X41)|~l1_lattices(X41)))&((m1_subset_1(esk9_1(X41),u1_struct_0(X41))|v6_lattices(X41)|(v2_struct_0(X41)|~l1_lattices(X41)))&(k2_lattices(X41,esk8_1(X41),esk9_1(X41))!=k2_lattices(X41,esk9_1(X41),esk8_1(X41))|v6_lattices(X41)|(v2_struct_0(X41)|~l1_lattices(X41)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 0.20/0.46  cnf(c_0_83, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.46  cnf(c_0_84, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk5_2(X1,X2))!=X2|k2_lattices(X1,esk5_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.46  cnf(c_0_85, negated_conjecture, (k2_lattices(esk12_0,k15_lattice3(esk12_0,k1_xboole_0),esk5_2(esk12_0,k15_lattice3(esk12_0,X1)))=k15_lattice3(esk12_0,k1_xboole_0)|v13_lattices(esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_36])])).
% 0.20/0.46  cnf(c_0_86, negated_conjecture, (~v13_lattices(esk12_0)|~l1_lattices(esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_73]), c_0_26])])).
% 0.20/0.46  cnf(c_0_87, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.20/0.46  cnf(c_0_88, negated_conjecture, (v6_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_32]), c_0_26])]), c_0_27])).
% 0.20/0.46  cnf(c_0_89, negated_conjecture, (k2_lattices(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,k1_xboole_0)),k15_lattice3(esk12_0,k1_xboole_0))!=k15_lattice3(esk12_0,k1_xboole_0)|~l1_lattices(esk12_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_36])]), c_0_27]), c_0_86])).
% 0.20/0.46  cnf(c_0_90, negated_conjecture, (k2_lattices(esk12_0,X1,esk5_2(esk12_0,k15_lattice3(esk12_0,X2)))=k2_lattices(esk12_0,esk5_2(esk12_0,k15_lattice3(esk12_0,X2)),X1)|~m1_subset_1(X1,u1_struct_0(esk12_0))|~l1_lattices(esk12_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_59]), c_0_88])]), c_0_27]), c_0_86])).
% 0.20/0.46  cnf(c_0_91, negated_conjecture, (k2_lattices(esk12_0,k15_lattice3(esk12_0,k1_xboole_0),esk5_2(esk12_0,k15_lattice3(esk12_0,k1_xboole_0)))!=k15_lattice3(esk12_0,k1_xboole_0)|~l1_lattices(esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_36])])).
% 0.20/0.46  cnf(c_0_92, negated_conjecture, (~l1_lattices(esk12_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_85]), c_0_86])).
% 0.20/0.46  cnf(c_0_93, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_21]), c_0_26])]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 94
% 0.20/0.46  # Proof object clause steps            : 63
% 0.20/0.46  # Proof object formula steps           : 31
% 0.20/0.46  # Proof object conjectures             : 43
% 0.20/0.46  # Proof object clause conjectures      : 40
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 22
% 0.20/0.46  # Proof object initial formulas used   : 15
% 0.20/0.46  # Proof object generating inferences   : 36
% 0.20/0.46  # Proof object simplifying inferences  : 75
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 17
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 57
% 0.20/0.46  # Removed in clause preprocessing      : 1
% 0.20/0.46  # Initial clauses in saturation        : 56
% 0.20/0.46  # Processed clauses                    : 812
% 0.20/0.46  # ...of these trivial                  : 2
% 0.20/0.46  # ...subsumed                          : 332
% 0.20/0.46  # ...remaining for further processing  : 478
% 0.20/0.46  # Other redundant clauses eliminated   : 7
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 55
% 0.20/0.46  # Backward-rewritten                   : 3
% 0.20/0.46  # Generated clauses                    : 2188
% 0.20/0.46  # ...of the previous two non-trivial   : 2074
% 0.20/0.46  # Contextual simplify-reflections      : 34
% 0.20/0.46  # Paramodulations                      : 2181
% 0.20/0.46  # Factorizations                       : 0
% 0.20/0.46  # Equation resolutions                 : 7
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 357
% 0.20/0.46  #    Positive orientable unit clauses  : 30
% 0.20/0.46  #    Positive unorientable unit clauses: 0
% 0.20/0.46  #    Negative unit clauses             : 4
% 0.20/0.46  #    Non-unit-clauses                  : 323
% 0.20/0.46  # Current number of unprocessed clauses: 1373
% 0.20/0.46  # ...number of literals in the above   : 5177
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 114
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 11473
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 4207
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 409
% 0.20/0.46  # Unit Clause-clause subsumption calls : 144
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 44
% 0.20/0.46  # BW rewrite match successes           : 1
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 66443
% 0.20/0.46  
% 0.20/0.46  # -------------------------------------------------
% 0.20/0.46  # User time                : 0.115 s
% 0.20/0.46  # System time              : 0.007 s
% 0.20/0.46  # Total time               : 0.123 s
% 0.20/0.46  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
