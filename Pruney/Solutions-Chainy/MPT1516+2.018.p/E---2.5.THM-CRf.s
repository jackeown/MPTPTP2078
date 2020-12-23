%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:08 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :  140 (160484 expanded)
%              Number of clauses        :  113 (60625 expanded)
%              Number of leaves         :   13 (38566 expanded)
%              Depth                    :   36
%              Number of atoms          :  602 (1031715 expanded)
%              Number of equality atoms :  145 (110903 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

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

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

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

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

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
    ! [X15] :
      ( ( l1_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( l2_lattices(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    & v10_lattices(esk8_0)
    & v4_lattice3(esk8_0)
    & l3_lattices(esk8_0)
    & ( v2_struct_0(esk8_0)
      | ~ v10_lattices(esk8_0)
      | ~ v13_lattices(esk8_0)
      | ~ l3_lattices(esk8_0)
      | k5_lattices(esk8_0) != k15_lattice3(esk8_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X19,X21,X22] :
      ( ( m1_subset_1(esk2_1(X19),u1_struct_0(X19))
        | ~ v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) )
      & ( k2_lattices(X19,esk2_1(X19),X21) = esk2_1(X19)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) )
      & ( k2_lattices(X19,X21,esk2_1(X19)) = esk2_1(X19)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) )
      & ( m1_subset_1(esk3_2(X19,X22),u1_struct_0(X19))
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) )
      & ( k2_lattices(X19,X22,esk3_2(X19,X22)) != X22
        | k2_lattices(X19,esk3_2(X19,X22),X22) != X22
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | v13_lattices(X19)
        | v2_struct_0(X19)
        | ~ l1_lattices(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

cnf(c_0_17,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l3_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X40,X41] :
      ( v2_struct_0(X40)
      | ~ l3_lattices(X40)
      | m1_subset_1(k15_lattice3(X40,X41),u1_struct_0(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( l1_lattices(esk8_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X30,X31,X32,X33] :
      ( ( r4_lattice3(X30,X32,X31)
        | X32 != k15_lattice3(X30,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v4_lattice3(X30)
        | ~ l3_lattices(X30)
        | v2_struct_0(X30)
        | ~ l3_lattices(X30) )
      & ( ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ r4_lattice3(X30,X33,X31)
        | r1_lattices(X30,X32,X33)
        | X32 != k15_lattice3(X30,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v4_lattice3(X30)
        | ~ l3_lattices(X30)
        | v2_struct_0(X30)
        | ~ l3_lattices(X30) )
      & ( m1_subset_1(esk5_3(X30,X31,X32),u1_struct_0(X30))
        | ~ r4_lattice3(X30,X32,X31)
        | X32 = k15_lattice3(X30,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v4_lattice3(X30)
        | ~ l3_lattices(X30)
        | v2_struct_0(X30)
        | ~ l3_lattices(X30) )
      & ( r4_lattice3(X30,esk5_3(X30,X31,X32),X31)
        | ~ r4_lattice3(X30,X32,X31)
        | X32 = k15_lattice3(X30,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v4_lattice3(X30)
        | ~ l3_lattices(X30)
        | v2_struct_0(X30)
        | ~ l3_lattices(X30) )
      & ( ~ r1_lattices(X30,X32,esk5_3(X30,X31,X32))
        | ~ r4_lattice3(X30,X32,X31)
        | X32 = k15_lattice3(X30,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v10_lattices(X30)
        | ~ v4_lattice3(X30)
        | ~ l3_lattices(X30)
        | v2_struct_0(X30)
        | ~ l3_lattices(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).

fof(c_0_25,plain,(
    ! [X5,X6] :
      ( ( k2_zfmisc_1(X5,X6) != k1_xboole_0
        | X5 = k1_xboole_0
        | X6 = k1_xboole_0 )
      & ( X5 != k1_xboole_0
        | k2_zfmisc_1(X5,X6) = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X5,X6) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_26,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( ( ~ r4_lattice3(X24,X25,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ r2_hidden(X27,X26)
        | r1_lattices(X24,X27,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( m1_subset_1(esk4_3(X24,X25,X28),u1_struct_0(X24))
        | r4_lattice3(X24,X25,X28)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( r2_hidden(esk4_3(X24,X25,X28),X28)
        | r4_lattice3(X24,X25,X28)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( ~ r1_lattices(X24,esk4_3(X24,X25,X28),X25)
        | r4_lattice3(X24,X25,X28)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_2(esk8_0,X1),u1_struct_0(esk8_0))
    | v13_lattices(esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk8_0,X1),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_18]),c_0_22])).

cnf(c_0_29,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X7,X8] : ~ r2_hidden(X7,k2_zfmisc_1(X7,X8)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X3)
    | r4_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),u1_struct_0(esk8_0))
    | v13_lattices(esk8_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( k2_lattices(X1,X2,esk2_1(X1)) = esk2_1(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_36,plain,(
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

cnf(c_0_37,plain,
    ( v2_struct_0(X2)
    | r1_lattices(X2,X4,X1)
    | X4 != k15_lattice3(X2,X3)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ r4_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(cn,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( r4_lattice3(esk8_0,X1,X2)
    | r2_hidden(esk4_3(esk8_0,X1,X2),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_18]),c_0_22])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),u1_struct_0(esk8_0))
    | m1_subset_1(esk2_1(esk8_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_21])]),c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( k2_lattices(esk8_0,X1,esk2_1(esk8_0)) = esk2_1(esk8_0)
    | m1_subset_1(esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_34]),c_0_21])]),c_0_22])).

fof(c_0_43,plain,(
    ! [X16,X17,X18] :
      ( ( ~ r1_lattices(X16,X17,X18)
        | k2_lattices(X16,X17,X18) = X17
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v8_lattices(X16)
        | ~ v9_lattices(X16)
        | ~ l3_lattices(X16) )
      & ( k2_lattices(X16,X17,X18) != X17
        | r1_lattices(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v8_lattices(X16)
        | ~ v9_lattices(X16)
        | ~ l3_lattices(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_44,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( v10_lattices(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_46,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( r1_lattices(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ r4_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_37]),c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( v4_lattice3(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),X2)
    | m1_subset_1(esk2_1(esk8_0),u1_struct_0(esk8_0))
    | r2_hidden(esk4_3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),X2),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_51,plain,(
    ! [X14] :
      ( v2_struct_0(X14)
      | ~ l1_lattices(X14)
      | m1_subset_1(k5_lattices(X14),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

cnf(c_0_52,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),esk2_1(esk8_0)) = esk2_1(esk8_0)
    | m1_subset_1(esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_28])).

cnf(c_0_53,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( v9_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_18])]),c_0_22])).

cnf(c_0_55,negated_conjecture,
    ( v8_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_45]),c_0_18])]),c_0_22])).

cnf(c_0_56,negated_conjecture,
    ( r1_lattices(esk8_0,k15_lattice3(esk8_0,X1),X2)
    | ~ r4_lattice3(esk8_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_45]),c_0_18])]),c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k1_xboole_0)
    | m1_subset_1(esk2_1(esk8_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),esk2_1(esk8_0)) = esk2_1(esk8_0)
    | r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),X3)
    | r2_hidden(esk4_3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),X3),X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( k2_lattices(esk8_0,X1,X2) = X1
    | ~ r1_lattices(esk8_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_18])]),c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( r1_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))
    | m1_subset_1(esk2_1(esk8_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_41])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk8_0),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_21]),c_0_22])).

cnf(c_0_63,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),esk2_1(esk8_0)) = esk2_1(esk8_0)
    | r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1))) = k15_lattice3(esk8_0,k1_xboole_0)
    | m1_subset_1(esk2_1(esk8_0),u1_struct_0(esk8_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_28])]),c_0_41])).

cnf(c_0_65,negated_conjecture,
    ( k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0)) = esk2_1(esk8_0)
    | m1_subset_1(esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),esk2_1(esk8_0)) = esk2_1(esk8_0)
    | r1_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_63]),c_0_52])).

cnf(c_0_67,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1))) = k15_lattice3(esk8_0,k1_xboole_0)
    | r4_lattice3(esk8_0,esk2_1(esk8_0),X2)
    | r2_hidden(esk4_3(esk8_0,esk2_1(esk8_0),X2),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_64])).

fof(c_0_68,plain,(
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

cnf(c_0_69,negated_conjecture,
    ( k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0)) = esk2_1(esk8_0)
    | r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),X2)
    | r2_hidden(esk4_3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),X2),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_65])).

fof(c_0_70,plain,(
    ! [X35,X36,X37] :
      ( ( ~ v6_lattices(X35)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | k2_lattices(X35,X36,X37) = k2_lattices(X35,X37,X36)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( m1_subset_1(esk6_1(X35),u1_struct_0(X35))
        | v6_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( m1_subset_1(esk7_1(X35),u1_struct_0(X35))
        | v6_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( k2_lattices(X35,esk6_1(X35),esk7_1(X35)) != k2_lattices(X35,esk7_1(X35),esk6_1(X35))
        | v6_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

cnf(c_0_71,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_72,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1))) = k15_lattice3(esk8_0,k1_xboole_0)
    | k2_lattices(esk8_0,k15_lattice3(esk8_0,X2),esk2_1(esk8_0)) = esk2_1(esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_66]),c_0_28])]),c_0_52])).

cnf(c_0_73,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1))) = k15_lattice3(esk8_0,k1_xboole_0)
    | r4_lattice3(esk8_0,esk2_1(esk8_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_67])).

cnf(c_0_74,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | k2_lattices(X1,esk3_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_76,negated_conjecture,
    ( k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0)) = esk2_1(esk8_0)
    | r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_69])).

cnf(c_0_77,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( v6_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_45]),c_0_18])]),c_0_22])).

cnf(c_0_79,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1))) = k15_lattice3(esk8_0,k1_xboole_0)
    | esk2_1(esk8_0) = k15_lattice3(esk8_0,X2)
    | ~ r1_lattices(esk8_0,k15_lattice3(esk8_0,X2),esk2_1(esk8_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_72]),c_0_28])]),c_0_64])).

cnf(c_0_80,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1))) = k15_lattice3(esk8_0,k1_xboole_0)
    | r1_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk2_1(esk8_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_73]),c_0_64])).

cnf(c_0_81,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]),c_0_58])).

cnf(c_0_82,negated_conjecture,
    ( v13_lattices(esk8_0)
    | k2_lattices(esk8_0,X1,esk3_2(esk8_0,X1)) != X1
    | k2_lattices(esk8_0,esk3_2(esk8_0,X1),X1) != X1
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_21]),c_0_22])).

cnf(c_0_83,negated_conjecture,
    ( k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0)) = esk2_1(esk8_0)
    | r1_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_76]),c_0_65])).

cnf(c_0_84,negated_conjecture,
    ( k2_lattices(esk8_0,X1,X2) = k2_lattices(esk8_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_21]),c_0_78])]),c_0_22])).

cnf(c_0_85,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1))) = k15_lattice3(esk8_0,k1_xboole_0)
    | k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X2))) = k15_lattice3(esk8_0,k1_xboole_0)
    | esk2_1(esk8_0) = k15_lattice3(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( k2_lattices(esk8_0,X1,k5_lattices(esk8_0)) = k5_lattices(esk8_0)
    | m1_subset_1(esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_34]),c_0_21])]),c_0_22])).

cnf(c_0_87,negated_conjecture,
    ( v13_lattices(esk8_0)
    | k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),esk3_2(esk8_0,k15_lattice3(esk8_0,X1))) != k15_lattice3(esk8_0,X1)
    | k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X1)) != k15_lattice3(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_28])).

cnf(c_0_88,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1))) = k15_lattice3(esk8_0,k1_xboole_0)
    | k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0)) = esk2_1(esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_83]),c_0_28])]),c_0_65])).

cnf(c_0_89,negated_conjecture,
    ( k2_lattices(esk8_0,X1,k15_lattice3(esk8_0,X2)) = k2_lattices(esk8_0,k15_lattice3(esk8_0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_28])).

cnf(c_0_90,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1))) = k15_lattice3(esk8_0,k1_xboole_0)
    | esk2_1(esk8_0) = k15_lattice3(esk8_0,k1_xboole_0) ),
    inference(ef,[status(thm)],[c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0)) = k5_lattices(esk8_0)
    | m1_subset_1(esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_28])).

cnf(c_0_92,negated_conjecture,
    ( k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0)) = esk2_1(esk8_0)
    | v13_lattices(esk8_0)
    | k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,k1_xboole_0)),k15_lattice3(esk8_0,k1_xboole_0)) != k15_lattice3(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X2)) = k2_lattices(esk8_0,k15_lattice3(esk8_0,X2),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))
    | k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0)) = esk2_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_65])).

cnf(c_0_94,negated_conjecture,
    ( r4_lattice3(esk8_0,k5_lattices(esk8_0),X1)
    | r2_hidden(esk4_3(esk8_0,k5_lattices(esk8_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_62])).

cnf(c_0_95,negated_conjecture,
    ( esk2_1(esk8_0) = k15_lattice3(esk8_0,k1_xboole_0)
    | v13_lattices(esk8_0)
    | k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,k1_xboole_0)),k15_lattice3(esk8_0,k1_xboole_0)) != k15_lattice3(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X2)) = k2_lattices(esk8_0,k15_lattice3(esk8_0,X2),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))
    | k2_lattices(esk8_0,k15_lattice3(esk8_0,X3),k5_lattices(esk8_0)) = k5_lattices(esk8_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0)) = esk2_1(esk8_0)
    | v13_lattices(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_88])).

cnf(c_0_98,negated_conjecture,
    ( r4_lattice3(esk8_0,k5_lattices(esk8_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0)) = k5_lattices(esk8_0)
    | esk2_1(esk8_0) = k15_lattice3(esk8_0,k1_xboole_0)
    | v13_lattices(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_90])).

cnf(c_0_100,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0)) = k5_lattices(esk8_0)
    | r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),X3)
    | r2_hidden(esk4_3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),X3),X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_91])).

cnf(c_0_101,negated_conjecture,
    ( k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0)) = esk2_1(esk8_0)
    | k2_lattices(esk8_0,X1,esk2_1(esk8_0)) = esk2_1(esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_97]),c_0_21])]),c_0_22])).

cnf(c_0_102,negated_conjecture,
    ( r1_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),k5_lattices(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_98]),c_0_62])])).

cnf(c_0_103,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0)) = k5_lattices(esk8_0)
    | k2_lattices(esk8_0,X2,k5_lattices(esk8_0)) = k5_lattices(esk8_0)
    | esk2_1(esk8_0) = k15_lattice3(esk8_0,k1_xboole_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_99]),c_0_21])]),c_0_22])).

cnf(c_0_104,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X3) != X2
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_105,negated_conjecture,
    ( k2_lattices(esk8_0,X1,k5_lattices(esk8_0)) = k2_lattices(esk8_0,k5_lattices(esk8_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_62])).

cnf(c_0_106,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0)) = k5_lattices(esk8_0)
    | r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0)) = esk2_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_101]),c_0_62])])).

cnf(c_0_108,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),k5_lattices(esk8_0)) = k15_lattice3(esk8_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_102]),c_0_62]),c_0_28])])).

cnf(c_0_109,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0)) = k5_lattices(esk8_0)
    | esk2_1(esk8_0) = k15_lattice3(esk8_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_103]),c_0_28])])).

cnf(c_0_110,negated_conjecture,
    ( r1_lattices(esk8_0,X1,X2)
    | k2_lattices(esk8_0,X1,X2) != X1
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_54]),c_0_55]),c_0_18])]),c_0_22])).

cnf(c_0_111,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0)) = k2_lattices(esk8_0,k5_lattices(esk8_0),k15_lattice3(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_28])).

cnf(c_0_112,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0)) = k5_lattices(esk8_0)
    | r1_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_106]),c_0_91])).

cnf(c_0_113,negated_conjecture,
    ( esk2_1(esk8_0) = k5_lattices(esk8_0)
    | ~ r1_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0))
    | ~ m1_subset_1(esk2_1(esk8_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_107]),c_0_62])])).

cnf(c_0_114,negated_conjecture,
    ( esk2_1(esk8_0) = k15_lattice3(esk8_0,k1_xboole_0)
    | k5_lattices(esk8_0) = k15_lattice3(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_115,negated_conjecture,
    ( r1_lattices(esk8_0,k5_lattices(esk8_0),k15_lattice3(esk8_0,X1))
    | k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0)) != k5_lattices(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_28]),c_0_62])])).

cnf(c_0_116,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1))) = k15_lattice3(esk8_0,k1_xboole_0)
    | k2_lattices(esk8_0,k15_lattice3(esk8_0,X2),k5_lattices(esk8_0)) = k5_lattices(esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_112]),c_0_28])]),c_0_91])).

cnf(c_0_117,negated_conjecture,
    ( k5_lattices(esk8_0) = k15_lattice3(esk8_0,k1_xboole_0)
    | ~ r1_lattices(esk8_0,k5_lattices(esk8_0),k15_lattice3(esk8_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_28])])).

cnf(c_0_118,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1))) = k15_lattice3(esk8_0,k1_xboole_0)
    | r1_lattices(esk8_0,k5_lattices(esk8_0),k15_lattice3(esk8_0,X2)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_119,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1))) = k15_lattice3(esk8_0,k1_xboole_0)
    | k5_lattices(esk8_0) = k15_lattice3(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_120,negated_conjecture,
    ( k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X2)) = k2_lattices(esk8_0,k15_lattice3(esk8_0,X2),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))
    | r1_lattices(esk8_0,k5_lattices(esk8_0),k15_lattice3(esk8_0,X3)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_96])).

cnf(c_0_121,negated_conjecture,
    ( k5_lattices(esk8_0) = k15_lattice3(esk8_0,k1_xboole_0)
    | v13_lattices(esk8_0)
    | k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,k1_xboole_0)),k15_lattice3(esk8_0,k1_xboole_0)) != k15_lattice3(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_119])).

cnf(c_0_122,negated_conjecture,
    ( k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X2)) = k2_lattices(esk8_0,k15_lattice3(esk8_0,X2),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))
    | k5_lattices(esk8_0) = k15_lattice3(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_117,c_0_120])).

cnf(c_0_123,negated_conjecture,
    ( k5_lattices(esk8_0) = k15_lattice3(esk8_0,k1_xboole_0)
    | v13_lattices(esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_119])).

cnf(c_0_124,negated_conjecture,
    ( k2_lattices(esk8_0,X1,k5_lattices(esk8_0)) = k5_lattices(esk8_0)
    | k5_lattices(esk8_0) = k15_lattice3(esk8_0,k1_xboole_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_123]),c_0_21])]),c_0_22])).

cnf(c_0_125,negated_conjecture,
    ( v2_struct_0(esk8_0)
    | ~ v10_lattices(esk8_0)
    | ~ v13_lattices(esk8_0)
    | ~ l3_lattices(esk8_0)
    | k5_lattices(esk8_0) != k15_lattice3(esk8_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_126,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0)) = k5_lattices(esk8_0)
    | k5_lattices(esk8_0) = k15_lattice3(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_124,c_0_28])).

cnf(c_0_127,negated_conjecture,
    ( k5_lattices(esk8_0) != k15_lattice3(esk8_0,k1_xboole_0)
    | ~ v13_lattices(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_18]),c_0_45])]),c_0_22])).

cnf(c_0_128,negated_conjecture,
    ( k5_lattices(esk8_0) = k15_lattice3(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_126])).

cnf(c_0_129,negated_conjecture,
    ( ~ v13_lattices(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_128])])).

cnf(c_0_130,negated_conjecture,
    ( m1_subset_1(esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[c_0_34,c_0_129])).

cnf(c_0_131,negated_conjecture,
    ( r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),X2)
    | r2_hidden(esk4_3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),X2),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_130])).

cnf(c_0_132,negated_conjecture,
    ( r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_131])).

cnf(c_0_133,negated_conjecture,
    ( v13_lattices(esk8_0)
    | k2_lattices(esk8_0,k5_lattices(esk8_0),esk3_2(esk8_0,k5_lattices(esk8_0))) != k5_lattices(esk8_0)
    | k2_lattices(esk8_0,esk3_2(esk8_0,k5_lattices(esk8_0)),k5_lattices(esk8_0)) != k5_lattices(esk8_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_62])).

cnf(c_0_134,negated_conjecture,
    ( r1_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_132]),c_0_130])])).

cnf(c_0_135,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,k1_xboole_0))) != k15_lattice3(esk8_0,k1_xboole_0)
    | k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,k1_xboole_0)),k15_lattice3(esk8_0,k1_xboole_0)) != k15_lattice3(esk8_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_128]),c_0_128]),c_0_128]),c_0_128]),c_0_128]),c_0_128]),c_0_129])).

cnf(c_0_136,negated_conjecture,
    ( k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1))) = k15_lattice3(esk8_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_134]),c_0_130]),c_0_28])])).

cnf(c_0_137,negated_conjecture,
    ( k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,k1_xboole_0)),k15_lattice3(esk8_0,k1_xboole_0)) != k15_lattice3(esk8_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_136])])).

cnf(c_0_138,negated_conjecture,
    ( k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X2)) = k2_lattices(esk8_0,k15_lattice3(esk8_0,X2),esk3_2(esk8_0,k15_lattice3(esk8_0,X1))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_130])).

cnf(c_0_139,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_137,c_0_138]),c_0_136])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:48:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 2.25/2.46  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 2.25/2.46  # and selection function HSelectMinInfpos.
% 2.25/2.46  #
% 2.25/2.46  # Preprocessing time       : 0.029 s
% 2.25/2.46  # Presaturation interreduction done
% 2.25/2.46  
% 2.25/2.46  # Proof found!
% 2.25/2.46  # SZS status Theorem
% 2.25/2.46  # SZS output start CNFRefutation
% 2.25/2.46  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 2.25/2.46  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.25/2.46  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 2.25/2.46  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 2.25/2.46  fof(d21_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X3=k15_lattice3(X1,X2)<=>(r4_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r4_lattice3(X1,X4,X2)=>r1_lattices(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 2.25/2.46  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.25/2.46  fof(d17_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r4_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 2.25/2.46  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.25/2.46  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 2.25/2.46  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 2.25/2.46  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 2.25/2.46  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 2.25/2.46  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 2.25/2.46  fof(c_0_13, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 2.25/2.46  fof(c_0_14, plain, ![X15]:((l1_lattices(X15)|~l3_lattices(X15))&(l2_lattices(X15)|~l3_lattices(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 2.25/2.46  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk8_0)&v10_lattices(esk8_0))&v4_lattice3(esk8_0))&l3_lattices(esk8_0))&(v2_struct_0(esk8_0)|~v10_lattices(esk8_0)|~v13_lattices(esk8_0)|~l3_lattices(esk8_0)|k5_lattices(esk8_0)!=k15_lattice3(esk8_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 2.25/2.46  fof(c_0_16, plain, ![X19, X21, X22]:(((m1_subset_1(esk2_1(X19),u1_struct_0(X19))|~v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))&((k2_lattices(X19,esk2_1(X19),X21)=esk2_1(X19)|~m1_subset_1(X21,u1_struct_0(X19))|~v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))&(k2_lattices(X19,X21,esk2_1(X19))=esk2_1(X19)|~m1_subset_1(X21,u1_struct_0(X19))|~v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))))&((m1_subset_1(esk3_2(X19,X22),u1_struct_0(X19))|~m1_subset_1(X22,u1_struct_0(X19))|v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))&(k2_lattices(X19,X22,esk3_2(X19,X22))!=X22|k2_lattices(X19,esk3_2(X19,X22),X22)!=X22|~m1_subset_1(X22,u1_struct_0(X19))|v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 2.25/2.46  cnf(c_0_17, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.25/2.46  cnf(c_0_18, negated_conjecture, (l3_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.25/2.46  fof(c_0_19, plain, ![X40, X41]:(v2_struct_0(X40)|~l3_lattices(X40)|m1_subset_1(k15_lattice3(X40,X41),u1_struct_0(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 2.25/2.46  cnf(c_0_20, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.25/2.46  cnf(c_0_21, negated_conjecture, (l1_lattices(esk8_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 2.25/2.46  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.25/2.46  cnf(c_0_23, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.25/2.46  fof(c_0_24, plain, ![X30, X31, X32, X33]:(((r4_lattice3(X30,X32,X31)|X32!=k15_lattice3(X30,X31)|~m1_subset_1(X32,u1_struct_0(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v4_lattice3(X30)|~l3_lattices(X30))|(v2_struct_0(X30)|~l3_lattices(X30)))&(~m1_subset_1(X33,u1_struct_0(X30))|(~r4_lattice3(X30,X33,X31)|r1_lattices(X30,X32,X33))|X32!=k15_lattice3(X30,X31)|~m1_subset_1(X32,u1_struct_0(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v4_lattice3(X30)|~l3_lattices(X30))|(v2_struct_0(X30)|~l3_lattices(X30))))&((m1_subset_1(esk5_3(X30,X31,X32),u1_struct_0(X30))|~r4_lattice3(X30,X32,X31)|X32=k15_lattice3(X30,X31)|~m1_subset_1(X32,u1_struct_0(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v4_lattice3(X30)|~l3_lattices(X30))|(v2_struct_0(X30)|~l3_lattices(X30)))&((r4_lattice3(X30,esk5_3(X30,X31,X32),X31)|~r4_lattice3(X30,X32,X31)|X32=k15_lattice3(X30,X31)|~m1_subset_1(X32,u1_struct_0(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v4_lattice3(X30)|~l3_lattices(X30))|(v2_struct_0(X30)|~l3_lattices(X30)))&(~r1_lattices(X30,X32,esk5_3(X30,X31,X32))|~r4_lattice3(X30,X32,X31)|X32=k15_lattice3(X30,X31)|~m1_subset_1(X32,u1_struct_0(X30))|(v2_struct_0(X30)|~v10_lattices(X30)|~v4_lattice3(X30)|~l3_lattices(X30))|(v2_struct_0(X30)|~l3_lattices(X30)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d21_lattice3])])])])])])).
% 2.25/2.46  fof(c_0_25, plain, ![X5, X6]:((k2_zfmisc_1(X5,X6)!=k1_xboole_0|(X5=k1_xboole_0|X6=k1_xboole_0))&((X5!=k1_xboole_0|k2_zfmisc_1(X5,X6)=k1_xboole_0)&(X6!=k1_xboole_0|k2_zfmisc_1(X5,X6)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 2.25/2.46  fof(c_0_26, plain, ![X24, X25, X26, X27, X28]:((~r4_lattice3(X24,X25,X26)|(~m1_subset_1(X27,u1_struct_0(X24))|(~r2_hidden(X27,X26)|r1_lattices(X24,X27,X25)))|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~l3_lattices(X24)))&((m1_subset_1(esk4_3(X24,X25,X28),u1_struct_0(X24))|r4_lattice3(X24,X25,X28)|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~l3_lattices(X24)))&((r2_hidden(esk4_3(X24,X25,X28),X28)|r4_lattice3(X24,X25,X28)|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~l3_lattices(X24)))&(~r1_lattices(X24,esk4_3(X24,X25,X28),X25)|r4_lattice3(X24,X25,X28)|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~l3_lattices(X24)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_lattice3])])])])])])])).
% 2.25/2.46  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_2(esk8_0,X1),u1_struct_0(esk8_0))|v13_lattices(esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 2.25/2.46  cnf(c_0_28, negated_conjecture, (m1_subset_1(k15_lattice3(esk8_0,X1),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_18]), c_0_22])).
% 2.25/2.46  cnf(c_0_29, plain, (r1_lattices(X2,X4,X1)|v2_struct_0(X2)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r4_lattice3(X2,X1,X3)|X4!=k15_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.25/2.46  fof(c_0_30, plain, ![X7, X8]:~r2_hidden(X7,k2_zfmisc_1(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 2.25/2.46  cnf(c_0_31, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.25/2.46  cnf(c_0_32, plain, (r2_hidden(esk4_3(X1,X2,X3),X3)|r4_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.25/2.46  cnf(c_0_33, plain, (m1_subset_1(esk2_1(X1),u1_struct_0(X1))|v2_struct_0(X1)|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.25/2.46  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),u1_struct_0(esk8_0))|v13_lattices(esk8_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 2.25/2.46  cnf(c_0_35, plain, (k2_lattices(X1,X2,esk2_1(X1))=esk2_1(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.25/2.46  fof(c_0_36, plain, ![X9]:(((((((~v2_struct_0(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9))&(v4_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v5_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v6_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v7_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v8_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v9_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 2.25/2.46  cnf(c_0_37, plain, (v2_struct_0(X2)|r1_lattices(X2,X4,X1)|X4!=k15_lattice3(X2,X3)|~l3_lattices(X2)|~v10_lattices(X2)|~v4_lattice3(X2)|~r4_lattice3(X2,X1,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))), inference(cn,[status(thm)],[c_0_29])).
% 2.25/2.46  cnf(c_0_38, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.25/2.46  cnf(c_0_39, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_31])).
% 2.25/2.46  cnf(c_0_40, negated_conjecture, (r4_lattice3(esk8_0,X1,X2)|r2_hidden(esk4_3(esk8_0,X1,X2),X2)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_18]), c_0_22])).
% 2.25/2.46  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),u1_struct_0(esk8_0))|m1_subset_1(esk2_1(esk8_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_21])]), c_0_22])).
% 2.25/2.46  cnf(c_0_42, negated_conjecture, (k2_lattices(esk8_0,X1,esk2_1(esk8_0))=esk2_1(esk8_0)|m1_subset_1(esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_34]), c_0_21])]), c_0_22])).
% 2.25/2.46  fof(c_0_43, plain, ![X16, X17, X18]:((~r1_lattices(X16,X17,X18)|k2_lattices(X16,X17,X18)=X17|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v8_lattices(X16)|~v9_lattices(X16)|~l3_lattices(X16)))&(k2_lattices(X16,X17,X18)!=X17|r1_lattices(X16,X17,X18)|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v8_lattices(X16)|~v9_lattices(X16)|~l3_lattices(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 2.25/2.46  cnf(c_0_44, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.25/2.46  cnf(c_0_45, negated_conjecture, (v10_lattices(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.25/2.46  cnf(c_0_46, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.25/2.46  cnf(c_0_47, plain, (r1_lattices(X1,k15_lattice3(X1,X2),X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~r4_lattice3(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_37]), c_0_23])).
% 2.25/2.46  cnf(c_0_48, negated_conjecture, (v4_lattice3(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.25/2.46  cnf(c_0_49, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 2.25/2.46  cnf(c_0_50, negated_conjecture, (r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),X2)|m1_subset_1(esk2_1(esk8_0),u1_struct_0(esk8_0))|r2_hidden(esk4_3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),X2),X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 2.25/2.46  fof(c_0_51, plain, ![X14]:(v2_struct_0(X14)|~l1_lattices(X14)|m1_subset_1(k5_lattices(X14),u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 2.25/2.46  cnf(c_0_52, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),esk2_1(esk8_0))=esk2_1(esk8_0)|m1_subset_1(esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_42, c_0_28])).
% 2.25/2.46  cnf(c_0_53, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.25/2.46  cnf(c_0_54, negated_conjecture, (v9_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_18])]), c_0_22])).
% 2.25/2.46  cnf(c_0_55, negated_conjecture, (v8_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_45]), c_0_18])]), c_0_22])).
% 2.25/2.46  cnf(c_0_56, negated_conjecture, (r1_lattices(esk8_0,k15_lattice3(esk8_0,X1),X2)|~r4_lattice3(esk8_0,X2,X1)|~m1_subset_1(X2,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_45]), c_0_18])]), c_0_22])).
% 2.25/2.46  cnf(c_0_57, negated_conjecture, (r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k1_xboole_0)|m1_subset_1(esk2_1(esk8_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 2.25/2.46  cnf(c_0_58, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 2.25/2.46  cnf(c_0_59, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),esk2_1(esk8_0))=esk2_1(esk8_0)|r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),X3)|r2_hidden(esk4_3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),X3),X3)), inference(spm,[status(thm)],[c_0_40, c_0_52])).
% 2.25/2.46  cnf(c_0_60, negated_conjecture, (k2_lattices(esk8_0,X1,X2)=X1|~r1_lattices(esk8_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_18])]), c_0_22])).
% 2.25/2.46  cnf(c_0_61, negated_conjecture, (r1_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))|m1_subset_1(esk2_1(esk8_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_41])).
% 2.25/2.46  cnf(c_0_62, negated_conjecture, (m1_subset_1(k5_lattices(esk8_0),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_21]), c_0_22])).
% 2.25/2.46  cnf(c_0_63, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),esk2_1(esk8_0))=esk2_1(esk8_0)|r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_59])).
% 2.25/2.46  cnf(c_0_64, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))=k15_lattice3(esk8_0,k1_xboole_0)|m1_subset_1(esk2_1(esk8_0),u1_struct_0(esk8_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_28])]), c_0_41])).
% 2.25/2.46  cnf(c_0_65, negated_conjecture, (k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0))=esk2_1(esk8_0)|m1_subset_1(esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_42, c_0_62])).
% 2.25/2.46  cnf(c_0_66, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),esk2_1(esk8_0))=esk2_1(esk8_0)|r1_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_63]), c_0_52])).
% 2.25/2.46  cnf(c_0_67, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))=k15_lattice3(esk8_0,k1_xboole_0)|r4_lattice3(esk8_0,esk2_1(esk8_0),X2)|r2_hidden(esk4_3(esk8_0,esk2_1(esk8_0),X2),X2)), inference(spm,[status(thm)],[c_0_40, c_0_64])).
% 2.25/2.46  fof(c_0_68, plain, ![X10, X11, X12]:(((k2_lattices(X10,X11,X12)=X11|~m1_subset_1(X12,u1_struct_0(X10))|X11!=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10)))&(k2_lattices(X10,X12,X11)=X11|~m1_subset_1(X12,u1_struct_0(X10))|X11!=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10))))&((m1_subset_1(esk1_2(X10,X11),u1_struct_0(X10))|X11=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10)))&(k2_lattices(X10,X11,esk1_2(X10,X11))!=X11|k2_lattices(X10,esk1_2(X10,X11),X11)!=X11|X11=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 2.25/2.46  cnf(c_0_69, negated_conjecture, (k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0))=esk2_1(esk8_0)|r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),X2)|r2_hidden(esk4_3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),X2),X2)), inference(spm,[status(thm)],[c_0_40, c_0_65])).
% 2.25/2.46  fof(c_0_70, plain, ![X35, X36, X37]:((~v6_lattices(X35)|(~m1_subset_1(X36,u1_struct_0(X35))|(~m1_subset_1(X37,u1_struct_0(X35))|k2_lattices(X35,X36,X37)=k2_lattices(X35,X37,X36)))|(v2_struct_0(X35)|~l1_lattices(X35)))&((m1_subset_1(esk6_1(X35),u1_struct_0(X35))|v6_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))&((m1_subset_1(esk7_1(X35),u1_struct_0(X35))|v6_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))&(k2_lattices(X35,esk6_1(X35),esk7_1(X35))!=k2_lattices(X35,esk7_1(X35),esk6_1(X35))|v6_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 2.25/2.46  cnf(c_0_71, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.25/2.46  cnf(c_0_72, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))=k15_lattice3(esk8_0,k1_xboole_0)|k2_lattices(esk8_0,k15_lattice3(esk8_0,X2),esk2_1(esk8_0))=esk2_1(esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_66]), c_0_28])]), c_0_52])).
% 2.25/2.46  cnf(c_0_73, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))=k15_lattice3(esk8_0,k1_xboole_0)|r4_lattice3(esk8_0,esk2_1(esk8_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_67])).
% 2.25/2.46  cnf(c_0_74, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 2.25/2.46  cnf(c_0_75, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|k2_lattices(X1,esk3_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.25/2.46  cnf(c_0_76, negated_conjecture, (k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0))=esk2_1(esk8_0)|r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_69])).
% 2.25/2.46  cnf(c_0_77, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 2.25/2.46  cnf(c_0_78, negated_conjecture, (v6_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_45]), c_0_18])]), c_0_22])).
% 2.25/2.46  cnf(c_0_79, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))=k15_lattice3(esk8_0,k1_xboole_0)|esk2_1(esk8_0)=k15_lattice3(esk8_0,X2)|~r1_lattices(esk8_0,k15_lattice3(esk8_0,X2),esk2_1(esk8_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_72]), c_0_28])]), c_0_64])).
% 2.25/2.46  cnf(c_0_80, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))=k15_lattice3(esk8_0,k1_xboole_0)|r1_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk2_1(esk8_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_73]), c_0_64])).
% 2.25/2.46  cnf(c_0_81, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]), c_0_58])).
% 2.25/2.46  cnf(c_0_82, negated_conjecture, (v13_lattices(esk8_0)|k2_lattices(esk8_0,X1,esk3_2(esk8_0,X1))!=X1|k2_lattices(esk8_0,esk3_2(esk8_0,X1),X1)!=X1|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_21]), c_0_22])).
% 2.25/2.46  cnf(c_0_83, negated_conjecture, (k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0))=esk2_1(esk8_0)|r1_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_76]), c_0_65])).
% 2.25/2.46  cnf(c_0_84, negated_conjecture, (k2_lattices(esk8_0,X1,X2)=k2_lattices(esk8_0,X2,X1)|~m1_subset_1(X2,u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_21]), c_0_78])]), c_0_22])).
% 2.25/2.46  cnf(c_0_85, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))=k15_lattice3(esk8_0,k1_xboole_0)|k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X2)))=k15_lattice3(esk8_0,k1_xboole_0)|esk2_1(esk8_0)=k15_lattice3(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 2.25/2.46  cnf(c_0_86, negated_conjecture, (k2_lattices(esk8_0,X1,k5_lattices(esk8_0))=k5_lattices(esk8_0)|m1_subset_1(esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_34]), c_0_21])]), c_0_22])).
% 2.25/2.46  cnf(c_0_87, negated_conjecture, (v13_lattices(esk8_0)|k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))!=k15_lattice3(esk8_0,X1)|k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X1))!=k15_lattice3(esk8_0,X1)), inference(spm,[status(thm)],[c_0_82, c_0_28])).
% 2.25/2.46  cnf(c_0_88, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))=k15_lattice3(esk8_0,k1_xboole_0)|k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0))=esk2_1(esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_83]), c_0_28])]), c_0_65])).
% 2.25/2.46  cnf(c_0_89, negated_conjecture, (k2_lattices(esk8_0,X1,k15_lattice3(esk8_0,X2))=k2_lattices(esk8_0,k15_lattice3(esk8_0,X2),X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_84, c_0_28])).
% 2.25/2.46  cnf(c_0_90, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))=k15_lattice3(esk8_0,k1_xboole_0)|esk2_1(esk8_0)=k15_lattice3(esk8_0,k1_xboole_0)), inference(ef,[status(thm)],[c_0_85])).
% 2.25/2.46  cnf(c_0_91, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0))=k5_lattices(esk8_0)|m1_subset_1(esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_86, c_0_28])).
% 2.25/2.46  cnf(c_0_92, negated_conjecture, (k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0))=esk2_1(esk8_0)|v13_lattices(esk8_0)|k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,k1_xboole_0)),k15_lattice3(esk8_0,k1_xboole_0))!=k15_lattice3(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 2.25/2.46  cnf(c_0_93, negated_conjecture, (k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X2))=k2_lattices(esk8_0,k15_lattice3(esk8_0,X2),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))|k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0))=esk2_1(esk8_0)), inference(spm,[status(thm)],[c_0_89, c_0_65])).
% 2.25/2.46  cnf(c_0_94, negated_conjecture, (r4_lattice3(esk8_0,k5_lattices(esk8_0),X1)|r2_hidden(esk4_3(esk8_0,k5_lattices(esk8_0),X1),X1)), inference(spm,[status(thm)],[c_0_40, c_0_62])).
% 2.25/2.46  cnf(c_0_95, negated_conjecture, (esk2_1(esk8_0)=k15_lattice3(esk8_0,k1_xboole_0)|v13_lattices(esk8_0)|k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,k1_xboole_0)),k15_lattice3(esk8_0,k1_xboole_0))!=k15_lattice3(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_90])).
% 2.25/2.46  cnf(c_0_96, negated_conjecture, (k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X2))=k2_lattices(esk8_0,k15_lattice3(esk8_0,X2),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))|k2_lattices(esk8_0,k15_lattice3(esk8_0,X3),k5_lattices(esk8_0))=k5_lattices(esk8_0)), inference(spm,[status(thm)],[c_0_89, c_0_91])).
% 2.25/2.46  cnf(c_0_97, negated_conjecture, (k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0))=esk2_1(esk8_0)|v13_lattices(esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_88])).
% 2.25/2.46  cnf(c_0_98, negated_conjecture, (r4_lattice3(esk8_0,k5_lattices(esk8_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_94])).
% 2.25/2.46  cnf(c_0_99, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0))=k5_lattices(esk8_0)|esk2_1(esk8_0)=k15_lattice3(esk8_0,k1_xboole_0)|v13_lattices(esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_90])).
% 2.25/2.46  cnf(c_0_100, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0))=k5_lattices(esk8_0)|r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),X3)|r2_hidden(esk4_3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),X3),X3)), inference(spm,[status(thm)],[c_0_40, c_0_91])).
% 2.25/2.46  cnf(c_0_101, negated_conjecture, (k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0))=esk2_1(esk8_0)|k2_lattices(esk8_0,X1,esk2_1(esk8_0))=esk2_1(esk8_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_97]), c_0_21])]), c_0_22])).
% 2.25/2.46  cnf(c_0_102, negated_conjecture, (r1_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),k5_lattices(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_98]), c_0_62])])).
% 2.25/2.46  cnf(c_0_103, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0))=k5_lattices(esk8_0)|k2_lattices(esk8_0,X2,k5_lattices(esk8_0))=k5_lattices(esk8_0)|esk2_1(esk8_0)=k15_lattice3(esk8_0,k1_xboole_0)|~m1_subset_1(X2,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_99]), c_0_21])]), c_0_22])).
% 2.25/2.46  cnf(c_0_104, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k2_lattices(X1,X2,X3)!=X2|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.25/2.46  cnf(c_0_105, negated_conjecture, (k2_lattices(esk8_0,X1,k5_lattices(esk8_0))=k2_lattices(esk8_0,k5_lattices(esk8_0),X1)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_84, c_0_62])).
% 2.25/2.46  cnf(c_0_106, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0))=k5_lattices(esk8_0)|r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X2)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_100])).
% 2.25/2.46  cnf(c_0_107, negated_conjecture, (k2_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0))=esk2_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_101]), c_0_62])])).
% 2.25/2.46  cnf(c_0_108, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),k5_lattices(esk8_0))=k15_lattice3(esk8_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_102]), c_0_62]), c_0_28])])).
% 2.25/2.46  cnf(c_0_109, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0))=k5_lattices(esk8_0)|esk2_1(esk8_0)=k15_lattice3(esk8_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_103]), c_0_28])])).
% 2.25/2.46  cnf(c_0_110, negated_conjecture, (r1_lattices(esk8_0,X1,X2)|k2_lattices(esk8_0,X1,X2)!=X1|~m1_subset_1(X2,u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_54]), c_0_55]), c_0_18])]), c_0_22])).
% 2.25/2.46  cnf(c_0_111, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0))=k2_lattices(esk8_0,k5_lattices(esk8_0),k15_lattice3(esk8_0,X1))), inference(spm,[status(thm)],[c_0_105, c_0_28])).
% 2.25/2.46  cnf(c_0_112, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0))=k5_lattices(esk8_0)|r1_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_106]), c_0_91])).
% 2.25/2.46  cnf(c_0_113, negated_conjecture, (esk2_1(esk8_0)=k5_lattices(esk8_0)|~r1_lattices(esk8_0,k5_lattices(esk8_0),esk2_1(esk8_0))|~m1_subset_1(esk2_1(esk8_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_107]), c_0_62])])).
% 2.25/2.46  cnf(c_0_114, negated_conjecture, (esk2_1(esk8_0)=k15_lattice3(esk8_0,k1_xboole_0)|k5_lattices(esk8_0)=k15_lattice3(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 2.25/2.46  cnf(c_0_115, negated_conjecture, (r1_lattices(esk8_0,k5_lattices(esk8_0),k15_lattice3(esk8_0,X1))|k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0))!=k5_lattices(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_28]), c_0_62])])).
% 2.25/2.46  cnf(c_0_116, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))=k15_lattice3(esk8_0,k1_xboole_0)|k2_lattices(esk8_0,k15_lattice3(esk8_0,X2),k5_lattices(esk8_0))=k5_lattices(esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_112]), c_0_28])]), c_0_91])).
% 2.25/2.46  cnf(c_0_117, negated_conjecture, (k5_lattices(esk8_0)=k15_lattice3(esk8_0,k1_xboole_0)|~r1_lattices(esk8_0,k5_lattices(esk8_0),k15_lattice3(esk8_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_28])])).
% 2.25/2.46  cnf(c_0_118, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))=k15_lattice3(esk8_0,k1_xboole_0)|r1_lattices(esk8_0,k5_lattices(esk8_0),k15_lattice3(esk8_0,X2))), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 2.25/2.46  cnf(c_0_119, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))=k15_lattice3(esk8_0,k1_xboole_0)|k5_lattices(esk8_0)=k15_lattice3(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 2.25/2.46  cnf(c_0_120, negated_conjecture, (k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X2))=k2_lattices(esk8_0,k15_lattice3(esk8_0,X2),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))|r1_lattices(esk8_0,k5_lattices(esk8_0),k15_lattice3(esk8_0,X3))), inference(spm,[status(thm)],[c_0_115, c_0_96])).
% 2.25/2.46  cnf(c_0_121, negated_conjecture, (k5_lattices(esk8_0)=k15_lattice3(esk8_0,k1_xboole_0)|v13_lattices(esk8_0)|k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,k1_xboole_0)),k15_lattice3(esk8_0,k1_xboole_0))!=k15_lattice3(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_119])).
% 2.25/2.46  cnf(c_0_122, negated_conjecture, (k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X2))=k2_lattices(esk8_0,k15_lattice3(esk8_0,X2),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))|k5_lattices(esk8_0)=k15_lattice3(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_117, c_0_120])).
% 2.25/2.46  cnf(c_0_123, negated_conjecture, (k5_lattices(esk8_0)=k15_lattice3(esk8_0,k1_xboole_0)|v13_lattices(esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_119])).
% 2.25/2.46  cnf(c_0_124, negated_conjecture, (k2_lattices(esk8_0,X1,k5_lattices(esk8_0))=k5_lattices(esk8_0)|k5_lattices(esk8_0)=k15_lattice3(esk8_0,k1_xboole_0)|~m1_subset_1(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_123]), c_0_21])]), c_0_22])).
% 2.25/2.46  cnf(c_0_125, negated_conjecture, (v2_struct_0(esk8_0)|~v10_lattices(esk8_0)|~v13_lattices(esk8_0)|~l3_lattices(esk8_0)|k5_lattices(esk8_0)!=k15_lattice3(esk8_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.25/2.46  cnf(c_0_126, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,X1),k5_lattices(esk8_0))=k5_lattices(esk8_0)|k5_lattices(esk8_0)=k15_lattice3(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_124, c_0_28])).
% 2.25/2.46  cnf(c_0_127, negated_conjecture, (k5_lattices(esk8_0)!=k15_lattice3(esk8_0,k1_xboole_0)|~v13_lattices(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125, c_0_18]), c_0_45])]), c_0_22])).
% 2.25/2.46  cnf(c_0_128, negated_conjecture, (k5_lattices(esk8_0)=k15_lattice3(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_108, c_0_126])).
% 2.25/2.46  cnf(c_0_129, negated_conjecture, (~v13_lattices(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_128])])).
% 2.25/2.46  cnf(c_0_130, negated_conjecture, (m1_subset_1(esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),u1_struct_0(esk8_0))), inference(sr,[status(thm)],[c_0_34, c_0_129])).
% 2.25/2.46  cnf(c_0_131, negated_conjecture, (r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),X2)|r2_hidden(esk4_3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),X2),X2)), inference(spm,[status(thm)],[c_0_40, c_0_130])).
% 2.25/2.46  cnf(c_0_132, negated_conjecture, (r4_lattice3(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_131])).
% 2.25/2.46  cnf(c_0_133, negated_conjecture, (v13_lattices(esk8_0)|k2_lattices(esk8_0,k5_lattices(esk8_0),esk3_2(esk8_0,k5_lattices(esk8_0)))!=k5_lattices(esk8_0)|k2_lattices(esk8_0,esk3_2(esk8_0,k5_lattices(esk8_0)),k5_lattices(esk8_0))!=k5_lattices(esk8_0)), inference(spm,[status(thm)],[c_0_82, c_0_62])).
% 2.25/2.46  cnf(c_0_134, negated_conjecture, (r1_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_132]), c_0_130])])).
% 2.25/2.46  cnf(c_0_135, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,k1_xboole_0)))!=k15_lattice3(esk8_0,k1_xboole_0)|k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,k1_xboole_0)),k15_lattice3(esk8_0,k1_xboole_0))!=k15_lattice3(esk8_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133, c_0_128]), c_0_128]), c_0_128]), c_0_128]), c_0_128]), c_0_128]), c_0_129])).
% 2.25/2.46  cnf(c_0_136, negated_conjecture, (k2_lattices(esk8_0,k15_lattice3(esk8_0,k1_xboole_0),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))=k15_lattice3(esk8_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_134]), c_0_130]), c_0_28])])).
% 2.25/2.46  cnf(c_0_137, negated_conjecture, (k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,k1_xboole_0)),k15_lattice3(esk8_0,k1_xboole_0))!=k15_lattice3(esk8_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_136])])).
% 2.25/2.46  cnf(c_0_138, negated_conjecture, (k2_lattices(esk8_0,esk3_2(esk8_0,k15_lattice3(esk8_0,X1)),k15_lattice3(esk8_0,X2))=k2_lattices(esk8_0,k15_lattice3(esk8_0,X2),esk3_2(esk8_0,k15_lattice3(esk8_0,X1)))), inference(spm,[status(thm)],[c_0_89, c_0_130])).
% 2.25/2.46  cnf(c_0_139, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_137, c_0_138]), c_0_136])]), ['proof']).
% 2.25/2.46  # SZS output end CNFRefutation
% 2.25/2.46  # Proof object total steps             : 140
% 2.25/2.46  # Proof object clause steps            : 113
% 2.25/2.46  # Proof object formula steps           : 27
% 2.25/2.46  # Proof object conjectures             : 93
% 2.25/2.46  # Proof object clause conjectures      : 90
% 2.25/2.46  # Proof object formula conjectures     : 3
% 2.25/2.46  # Proof object initial clauses used    : 23
% 2.25/2.46  # Proof object initial formulas used   : 13
% 2.25/2.46  # Proof object generating inferences   : 80
% 2.25/2.46  # Proof object simplifying inferences  : 116
% 2.25/2.46  # Training examples: 0 positive, 0 negative
% 2.25/2.46  # Parsed axioms                        : 13
% 2.25/2.46  # Removed by relevancy pruning/SinE    : 0
% 2.25/2.46  # Initial clauses                      : 44
% 2.25/2.46  # Removed in clause preprocessing      : 1
% 2.25/2.46  # Initial clauses in saturation        : 43
% 2.25/2.46  # Processed clauses                    : 8249
% 2.25/2.46  # ...of these trivial                  : 91
% 2.25/2.46  # ...subsumed                          : 4168
% 2.25/2.46  # ...remaining for further processing  : 3990
% 2.25/2.46  # Other redundant clauses eliminated   : 8
% 2.25/2.46  # Clauses deleted for lack of memory   : 0
% 2.25/2.46  # Backward-subsumed                    : 662
% 2.25/2.46  # Backward-rewritten                   : 3047
% 2.25/2.46  # Generated clauses                    : 173845
% 2.25/2.46  # ...of the previous two non-trivial   : 173862
% 2.25/2.46  # Contextual simplify-reflections      : 590
% 2.25/2.46  # Paramodulations                      : 173797
% 2.25/2.46  # Factorizations                       : 27
% 2.25/2.46  # Equation resolutions                 : 9
% 2.25/2.46  # Propositional unsat checks           : 0
% 2.25/2.46  #    Propositional check models        : 0
% 2.25/2.46  #    Propositional check unsatisfiable : 0
% 2.25/2.46  #    Propositional clauses             : 0
% 2.25/2.46  #    Propositional clauses after purity: 0
% 2.25/2.46  #    Propositional unsat core size     : 0
% 2.25/2.46  #    Propositional preprocessing time  : 0.000
% 2.25/2.46  #    Propositional encoding time       : 0.000
% 2.25/2.46  #    Propositional solver time         : 0.000
% 2.25/2.46  #    Success case prop preproc time    : 0.000
% 2.25/2.46  #    Success case prop encoding time   : 0.000
% 2.25/2.46  #    Success case prop solver time     : 0.000
% 2.25/2.46  # Current number of processed clauses  : 220
% 2.25/2.46  #    Positive orientable unit clauses  : 35
% 2.25/2.46  #    Positive unorientable unit clauses: 2
% 2.25/2.46  #    Negative unit clauses             : 4
% 2.25/2.46  #    Non-unit-clauses                  : 179
% 2.25/2.46  # Current number of unprocessed clauses: 163382
% 2.25/2.46  # ...number of literals in the above   : 868703
% 2.25/2.46  # Current number of archived formulas  : 0
% 2.25/2.46  # Current number of archived clauses   : 3764
% 2.25/2.46  # Clause-clause subsumption calls (NU) : 3840849
% 2.25/2.46  # Rec. Clause-clause subsumption calls : 333532
% 2.25/2.46  # Non-unit clause-clause subsumptions  : 5400
% 2.25/2.46  # Unit Clause-clause subsumption calls : 5175
% 2.25/2.46  # Rewrite failures with RHS unbound    : 0
% 2.25/2.46  # BW rewrite match attempts            : 198
% 2.25/2.46  # BW rewrite match successes           : 26
% 2.25/2.46  # Condensation attempts                : 0
% 2.25/2.46  # Condensation successes               : 0
% 2.25/2.46  # Termbank termtop insertions          : 6845480
% 2.25/2.47  
% 2.25/2.47  # -------------------------------------------------
% 2.25/2.47  # User time                : 2.078 s
% 2.25/2.47  # System time              : 0.056 s
% 2.25/2.47  # Total time               : 2.135 s
% 2.25/2.47  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
