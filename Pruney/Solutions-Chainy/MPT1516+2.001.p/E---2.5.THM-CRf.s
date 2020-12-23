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
% DateTime   : Thu Dec  3 11:15:06 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  151 (9178 expanded)
%              Number of clauses        :  116 (3247 expanded)
%              Number of leaves         :   17 (2255 expanded)
%              Depth                    :   27
%              Number of atoms          :  614 (58194 expanded)
%              Number of equality atoms :  106 (5433 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).

fof(t23_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => r1_lattices(X1,k4_lattices(X1,X2,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(c_0_17,plain,(
    ! [X21] :
      ( v2_struct_0(X21)
      | ~ l1_lattices(X21)
      | m1_subset_1(k5_lattices(X21),u1_struct_0(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_18,plain,(
    ! [X22] :
      ( ( l1_lattices(X22)
        | ~ l3_lattices(X22) )
      & ( l2_lattices(X22)
        | ~ l3_lattices(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_19,negated_conjecture,(
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

fof(c_0_20,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v10_lattices(esk5_0)
    & v4_lattice3(esk5_0)
    & l3_lattices(esk5_0)
    & ( v2_struct_0(esk5_0)
      | ~ v10_lattices(esk5_0)
      | ~ v13_lattices(esk5_0)
      | ~ l3_lattices(esk5_0)
      | k5_lattices(esk5_0) != k15_lattice3(esk5_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_24,plain,(
    ! [X40,X41] :
      ( v2_struct_0(X40)
      | ~ l3_lattices(X40)
      | m1_subset_1(k15_lattice3(X40,X41),u1_struct_0(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_25,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X23,X24,X25] :
      ( v2_struct_0(X23)
      | ~ v6_lattices(X23)
      | ~ l1_lattices(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | k4_lattices(X23,X24,X25) = k2_lattices(X23,X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

cnf(c_0_28,plain,
    ( m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( l3_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X18,X19,X20] :
      ( v2_struct_0(X18)
      | ~ v6_lattices(X18)
      | ~ l1_lattices(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | m1_subset_1(k4_lattices(X18,X19,X20),u1_struct_0(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X44,X45,X46,X48] :
      ( ( m1_subset_1(esk4_3(X44,X45,X46),u1_struct_0(X44))
        | r3_lattices(X44,k15_lattice3(X44,X45),k15_lattice3(X44,X46))
        | v2_struct_0(X44)
        | ~ v10_lattices(X44)
        | ~ v4_lattice3(X44)
        | ~ l3_lattices(X44) )
      & ( r2_hidden(esk4_3(X44,X45,X46),X45)
        | r3_lattices(X44,k15_lattice3(X44,X45),k15_lattice3(X44,X46))
        | v2_struct_0(X44)
        | ~ v10_lattices(X44)
        | ~ v4_lattice3(X44)
        | ~ l3_lattices(X44) )
      & ( ~ m1_subset_1(X48,u1_struct_0(X44))
        | ~ r3_lattices(X44,esk4_3(X44,X45,X46),X48)
        | ~ r2_hidden(X48,X46)
        | r3_lattices(X44,k15_lattice3(X44,X45),k15_lattice3(X44,X46))
        | v2_struct_0(X44)
        | ~ v10_lattices(X44)
        | ~ v4_lattice3(X44)
        | ~ l3_lattices(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).

fof(c_0_36,plain,(
    ! [X42,X43] :
      ( ( X43 = k15_lattice3(X42,a_2_3_lattice3(X42,X43))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v10_lattices(X42)
        | ~ v4_lattice3(X42)
        | ~ l3_lattices(X42) )
      & ( X43 = k16_lattice3(X42,a_2_4_lattice3(X42,X43))
        | ~ m1_subset_1(X43,u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v10_lattices(X42)
        | ~ v4_lattice3(X42)
        | ~ l3_lattices(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk5_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

fof(c_0_39,plain,(
    ! [X29,X30,X31] :
      ( v2_struct_0(X29)
      | ~ v6_lattices(X29)
      | ~ v8_lattices(X29)
      | ~ l3_lattices(X29)
      | ~ m1_subset_1(X30,u1_struct_0(X29))
      | ~ m1_subset_1(X31,u1_struct_0(X29))
      | r1_lattices(X29,k4_lattices(X29,X30,X31),X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_lattices])])])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk5_0,X1),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_30])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( X1 = k15_lattice3(X2,a_2_3_lattice3(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( v4_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( v10_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( k4_lattices(esk5_0,X1,k5_lattices(esk5_0)) = k2_lattices(esk5_0,X1,k5_lattices(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l1_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_30])).

fof(c_0_48,plain,(
    ! [X14,X15,X16] :
      ( ( k2_lattices(X14,X15,X16) = X15
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | X15 != k5_lattices(X14)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v13_lattices(X14)
        | v2_struct_0(X14)
        | ~ l1_lattices(X14) )
      & ( k2_lattices(X14,X16,X15) = X15
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | X15 != k5_lattices(X14)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v13_lattices(X14)
        | v2_struct_0(X14)
        | ~ l1_lattices(X14) )
      & ( m1_subset_1(esk1_2(X14,X15),u1_struct_0(X14))
        | X15 = k5_lattices(X14)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v13_lattices(X14)
        | v2_struct_0(X14)
        | ~ l1_lattices(X14) )
      & ( k2_lattices(X14,X15,esk1_2(X14,X15)) != X15
        | k2_lattices(X14,esk1_2(X14,X15),X15) != X15
        | X15 = k5_lattices(X14)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ v13_lattices(X14)
        | v2_struct_0(X14)
        | ~ l1_lattices(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | r1_lattices(X1,k4_lattices(X1,X2,X3),X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( k4_lattices(esk5_0,X1,k15_lattice3(esk5_0,X2)) = k2_lattices(esk5_0,X1,k15_lattice3(esk5_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l1_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_40]),c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk5_0,X1,k15_lattice3(esk5_0,X2)),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l1_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_30])).

fof(c_0_52,plain,(
    ! [X26,X27,X28] :
      ( ( ~ r3_lattices(X26,X27,X28)
        | r1_lattices(X26,X27,X28)
        | v2_struct_0(X26)
        | ~ v6_lattices(X26)
        | ~ v8_lattices(X26)
        | ~ v9_lattices(X26)
        | ~ l3_lattices(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ m1_subset_1(X28,u1_struct_0(X26)) )
      & ( ~ r1_lattices(X26,X27,X28)
        | r3_lattices(X26,X27,X28)
        | v2_struct_0(X26)
        | ~ v6_lattices(X26)
        | ~ v8_lattices(X26)
        | ~ v9_lattices(X26)
        | ~ l3_lattices(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ m1_subset_1(X28,u1_struct_0(X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_53,plain,
    ( r3_lattices(X1,k15_lattice3(X1,k1_xboole_0),k15_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,k5_lattices(esk5_0))) = k5_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_38]),c_0_45]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)) = k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0))
    | ~ l1_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_40])).

fof(c_0_56,plain,(
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

cnf(c_0_57,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_58,plain,(
    ! [X35,X37,X38] :
      ( ( m1_subset_1(esk2_1(X35),u1_struct_0(X35))
        | ~ v13_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( k2_lattices(X35,esk2_1(X35),X37) = esk2_1(X35)
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | ~ v13_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( k2_lattices(X35,X37,esk2_1(X35)) = esk2_1(X35)
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | ~ v13_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( m1_subset_1(esk3_2(X35,X38),u1_struct_0(X35))
        | ~ m1_subset_1(X38,u1_struct_0(X35))
        | v13_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( k2_lattices(X35,X38,esk3_2(X35,X38)) != X38
        | k2_lattices(X35,esk3_2(X35,X38),X38) != X38
        | ~ m1_subset_1(X38,u1_struct_0(X35))
        | v13_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

cnf(c_0_59,negated_conjecture,
    ( r1_lattices(esk5_0,k4_lattices(esk5_0,X1,k15_lattice3(esk5_0,X2)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_40]),c_0_29])]),c_0_30])).

cnf(c_0_60,negated_conjecture,
    ( k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)) = k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))
    | ~ l1_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_40])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)),u1_struct_0(esk5_0))
    | ~ l1_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_40])).

cnf(c_0_62,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( r3_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k5_lattices(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_45]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_64,negated_conjecture,
    ( k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)) = k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0))
    | ~ v6_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_22]),c_0_29])])).

cnf(c_0_65,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v13_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_57]),c_0_21])).

cnf(c_0_67,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( r1_lattices(esk5_0,k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X1))
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_40])).

cnf(c_0_69,negated_conjecture,
    ( k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)) = k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))
    | ~ v6_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_22]),c_0_29])])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)),u1_struct_0(esk5_0))
    | ~ v6_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_22]),c_0_29])])).

cnf(c_0_71,negated_conjecture,
    ( r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k5_lattices(esk5_0))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_38]),c_0_40]),c_0_29])]),c_0_30])).

cnf(c_0_72,negated_conjecture,
    ( r1_lattices(esk5_0,k4_lattices(esk5_0,X1,k5_lattices(esk5_0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_38]),c_0_29])]),c_0_30])).

cnf(c_0_73,negated_conjecture,
    ( k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)) = k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_74,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)) = k5_lattices(esk5_0)
    | ~ v13_lattices(esk5_0)
    | ~ l1_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_40]),c_0_30])).

cnf(c_0_75,negated_conjecture,
    ( v13_lattices(esk5_0)
    | m1_subset_1(esk3_2(esk5_0,k15_lattice3(esk5_0,X1)),u1_struct_0(esk5_0))
    | ~ l1_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_40]),c_0_30])).

cnf(c_0_76,negated_conjecture,
    ( r1_lattices(esk5_0,k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X1))
    | ~ v8_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_65]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_77,negated_conjecture,
    ( k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)) = k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_65]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_65]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_79,negated_conjecture,
    ( r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k5_lattices(esk5_0))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_65]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_80,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_81,negated_conjecture,
    ( r1_lattices(esk5_0,k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)),k15_lattice3(esk5_0,X1))
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_40]),c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)) = k5_lattices(esk5_0)
    | ~ v13_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_22]),c_0_29])])).

cnf(c_0_83,negated_conjecture,
    ( v13_lattices(esk5_0)
    | m1_subset_1(esk3_2(esk5_0,k15_lattice3(esk5_0,X1)),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_22]),c_0_29])])).

fof(c_0_84,plain,(
    ! [X32,X33,X34] :
      ( v2_struct_0(X32)
      | ~ v4_lattices(X32)
      | ~ l2_lattices(X32)
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | ~ m1_subset_1(X34,u1_struct_0(X32))
      | ~ r1_lattices(X32,X33,X34)
      | ~ r1_lattices(X32,X34,X33)
      | X33 = X34 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).

cnf(c_0_85,negated_conjecture,
    ( r1_lattices(esk5_0,k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X1))
    | ~ v8_lattices(esk5_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_86,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)),u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_78,c_0_77])).

cnf(c_0_88,negated_conjecture,
    ( r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k5_lattices(esk5_0))
    | ~ v9_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_89,negated_conjecture,
    ( r1_lattices(esk5_0,k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)),k15_lattice3(esk5_0,X1))
    | ~ v8_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_65]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_90,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)) = k5_lattices(esk5_0)
    | m1_subset_1(esk3_2(esk5_0,k15_lattice3(esk5_0,X2)),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

fof(c_0_91,plain,(
    ! [X11,X12,X13] :
      ( v2_struct_0(X11)
      | ~ v6_lattices(X11)
      | ~ l1_lattices(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | ~ m1_subset_1(X13,u1_struct_0(X11))
      | k4_lattices(X11,X12,X13) = k4_lattices(X11,X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_92,negated_conjecture,
    ( k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,k15_lattice3(esk5_0,X1))) = k15_lattice3(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_40]),c_0_45]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk5_0,X1,k5_lattices(esk5_0)),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l1_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_38]),c_0_30])).

cnf(c_0_94,plain,
    ( v2_struct_0(X1)
    | X2 = X3
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattices(X1,X2,X3)
    | ~ r1_lattices(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_95,negated_conjecture,
    ( r1_lattices(esk5_0,k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_80]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_96,plain,
    ( r1_lattices(X1,k15_lattice3(X1,k1_xboole_0),k15_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_53]),c_0_65]),c_0_80]),c_0_86]),c_0_31]),c_0_31])).

cnf(c_0_97,negated_conjecture,
    ( k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)))) = k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_87]),c_0_45]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_98,negated_conjecture,
    ( r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k5_lattices(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_86]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_99,negated_conjecture,
    ( r1_lattices(esk5_0,k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)),k15_lattice3(esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_80]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_100,negated_conjecture,
    ( k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,X1)))) = esk3_2(esk5_0,k15_lattice3(esk5_0,X1))
    | k2_lattices(esk5_0,k15_lattice3(esk5_0,X2),k5_lattices(esk5_0)) = k5_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_90]),c_0_45]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_101,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_102,negated_conjecture,
    ( r3_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k15_lattice3(esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_92]),c_0_45]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)),u1_struct_0(esk5_0))
    | ~ l1_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_40])).

cnf(c_0_104,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)) = k15_lattice3(esk5_0,X1)
    | ~ r1_lattices(esk5_0,k15_lattice3(esk5_0,X1),k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)))
    | ~ l2_lattices(esk5_0)
    | ~ v4_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_87]),c_0_40])]),c_0_30])).

cnf(c_0_105,negated_conjecture,
    ( r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_45]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_106,negated_conjecture,
    ( k5_lattices(esk5_0) = k15_lattice3(esk5_0,k1_xboole_0)
    | ~ r1_lattices(esk5_0,k5_lattices(esk5_0),k15_lattice3(esk5_0,k1_xboole_0))
    | ~ l2_lattices(esk5_0)
    | ~ v4_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_98]),c_0_40]),c_0_38])]),c_0_30])).

cnf(c_0_107,negated_conjecture,
    ( k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,X1)))) = esk3_2(esk5_0,k15_lattice3(esk5_0,X1))
    | r1_lattices(esk5_0,k5_lattices(esk5_0),k15_lattice3(esk5_0,X2)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_108,negated_conjecture,
    ( k4_lattices(esk5_0,X1,k15_lattice3(esk5_0,X2)) = k4_lattices(esk5_0,k15_lattice3(esk5_0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l1_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_40]),c_0_30])).

cnf(c_0_109,negated_conjecture,
    ( r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k15_lattice3(esk5_0,X1))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_102]),c_0_40]),c_0_40]),c_0_29])]),c_0_30])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)),u1_struct_0(esk5_0))
    | ~ v6_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_22]),c_0_29])])).

cnf(c_0_111,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k15_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,k1_xboole_0)
    | ~ l2_lattices(esk5_0)
    | ~ v4_lattices(esk5_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_112,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_113,negated_conjecture,
    ( k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,X1)))) = esk3_2(esk5_0,k15_lattice3(esk5_0,X1))
    | k5_lattices(esk5_0) = k15_lattice3(esk5_0,k1_xboole_0)
    | ~ l2_lattices(esk5_0)
    | ~ v4_lattices(esk5_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_114,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)) = k2_lattices(esk5_0,k15_lattice3(esk5_0,X2),k15_lattice3(esk5_0,X1))
    | ~ l1_lattices(esk5_0)
    | ~ v6_lattices(esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_40]),c_0_77]),c_0_77])).

cnf(c_0_115,negated_conjecture,
    ( r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k15_lattice3(esk5_0,X1))
    | ~ v9_lattices(esk5_0)
    | ~ v8_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_65]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_116,negated_conjecture,
    ( m1_subset_1(k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_65]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_117,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k15_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,k1_xboole_0)
    | ~ v4_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_29])])).

cnf(c_0_118,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_119,negated_conjecture,
    ( k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,X1)))) = esk3_2(esk5_0,k15_lattice3(esk5_0,X1))
    | k5_lattices(esk5_0) = k15_lattice3(esk5_0,k1_xboole_0)
    | ~ v4_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_112]),c_0_29])])).

cnf(c_0_120,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)) = k2_lattices(esk5_0,k15_lattice3(esk5_0,X2),k15_lattice3(esk5_0,X1))
    | ~ v6_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_22]),c_0_29])])).

cnf(c_0_121,negated_conjecture,
    ( r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k15_lattice3(esk5_0,X1))
    | ~ v9_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_80]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_122,negated_conjecture,
    ( m1_subset_1(k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_116,c_0_73])).

cnf(c_0_123,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k15_lattice3(esk5_0,X1)) = k15_lattice3(esk5_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_124,negated_conjecture,
    ( k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,X1)))) = esk3_2(esk5_0,k15_lattice3(esk5_0,X1))
    | k5_lattices(esk5_0) = k15_lattice3(esk5_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_118]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_125,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)) = k2_lattices(esk5_0,k15_lattice3(esk5_0,X2),k15_lattice3(esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_65]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_126,negated_conjecture,
    ( r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k15_lattice3(esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_86]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_127,negated_conjecture,
    ( k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)))) = k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_122]),c_0_45]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_128,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | k2_lattices(X1,esk3_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_129,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),esk3_2(esk5_0,k15_lattice3(esk5_0,X1))) = k15_lattice3(esk5_0,k1_xboole_0)
    | k5_lattices(esk5_0) = k15_lattice3(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_130,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,k1_xboole_0)) = k15_lattice3(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_125,c_0_123])).

cnf(c_0_131,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)) = k15_lattice3(esk5_0,X1)
    | ~ r1_lattices(esk5_0,k15_lattice3(esk5_0,X1),k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)))
    | ~ l2_lattices(esk5_0)
    | ~ v4_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_99]),c_0_122]),c_0_40])]),c_0_30])).

cnf(c_0_132,negated_conjecture,
    ( r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_133,negated_conjecture,
    ( k5_lattices(esk5_0) = k15_lattice3(esk5_0,k1_xboole_0)
    | v13_lattices(esk5_0)
    | k2_lattices(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,k1_xboole_0)),k15_lattice3(esk5_0,k1_xboole_0)) != k15_lattice3(esk5_0,k1_xboole_0)
    | ~ l1_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_40])]),c_0_30])).

cnf(c_0_134,negated_conjecture,
    ( k2_lattices(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,X1)),k15_lattice3(esk5_0,k1_xboole_0)) = k15_lattice3(esk5_0,k1_xboole_0)
    | k5_lattices(esk5_0) = k15_lattice3(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_130,c_0_124])).

cnf(c_0_135,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k5_lattices(esk5_0)) = k15_lattice3(esk5_0,k1_xboole_0)
    | ~ l2_lattices(esk5_0)
    | ~ v4_lattices(esk5_0) ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_136,negated_conjecture,
    ( k5_lattices(esk5_0) = k15_lattice3(esk5_0,k1_xboole_0)
    | v13_lattices(esk5_0)
    | ~ l1_lattices(esk5_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_137,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k5_lattices(esk5_0)) = k15_lattice3(esk5_0,k1_xboole_0)
    | ~ v4_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_112]),c_0_29])])).

cnf(c_0_138,negated_conjecture,
    ( k5_lattices(esk5_0) = k15_lattice3(esk5_0,k1_xboole_0)
    | v13_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_22]),c_0_29])])).

cnf(c_0_139,negated_conjecture,
    ( v2_struct_0(esk5_0)
    | ~ v10_lattices(esk5_0)
    | ~ v13_lattices(esk5_0)
    | ~ l3_lattices(esk5_0)
    | k5_lattices(esk5_0) != k15_lattice3(esk5_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_140,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k5_lattices(esk5_0)) = k15_lattice3(esk5_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_118]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_141,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)) = k5_lattices(esk5_0)
    | k5_lattices(esk5_0) = k15_lattice3(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_138])).

cnf(c_0_142,negated_conjecture,
    ( k5_lattices(esk5_0) != k15_lattice3(esk5_0,k1_xboole_0)
    | ~ v13_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_29]),c_0_46])]),c_0_30])).

cnf(c_0_143,negated_conjecture,
    ( k5_lattices(esk5_0) = k15_lattice3(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_140,c_0_141])).

cnf(c_0_144,negated_conjecture,
    ( ~ v13_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_142,c_0_143])])).

cnf(c_0_145,negated_conjecture,
    ( m1_subset_1(esk3_2(esk5_0,k15_lattice3(esk5_0,X1)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[c_0_83,c_0_144])).

cnf(c_0_146,negated_conjecture,
    ( k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,X1)))) = esk3_2(esk5_0,k15_lattice3(esk5_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_145]),c_0_45]),c_0_46]),c_0_29])]),c_0_30])).

cnf(c_0_147,negated_conjecture,
    ( k2_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),esk3_2(esk5_0,k15_lattice3(esk5_0,X1))) = k15_lattice3(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_123,c_0_146])).

cnf(c_0_148,negated_conjecture,
    ( k2_lattices(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,X1)),k15_lattice3(esk5_0,k1_xboole_0)) = k15_lattice3(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_130,c_0_146])).

cnf(c_0_149,negated_conjecture,
    ( ~ l1_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_147]),c_0_148]),c_0_40])]),c_0_144]),c_0_30])).

cnf(c_0_150,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_22]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n009.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 11:20:56 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 1.69/1.91  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 1.69/1.91  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 1.69/1.91  #
% 1.69/1.91  # Preprocessing time       : 0.029 s
% 1.69/1.91  # Presaturation interreduction done
% 1.69/1.91  
% 1.69/1.91  # Proof found!
% 1.69/1.91  # SZS status Theorem
% 1.69/1.91  # SZS output start CNFRefutation
% 1.69/1.91  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 1.69/1.91  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 1.69/1.91  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 1.69/1.91  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.69/1.91  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 1.69/1.91  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.69/1.91  fof(redefinition_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 1.69/1.91  fof(dt_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_lattices)).
% 1.69/1.91  fof(t48_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattice3)).
% 1.69/1.91  fof(t45_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k15_lattice3(X1,a_2_3_lattice3(X1,X2))&X2=k16_lattice3(X1,a_2_4_lattice3(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_lattice3)).
% 1.69/1.91  fof(t23_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>r1_lattices(X1,k4_lattices(X1,X2,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_lattices)).
% 1.69/1.91  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 1.69/1.91  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 1.69/1.91  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 1.69/1.91  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 1.69/1.91  fof(t26_lattices, axiom, ![X1]:(((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_lattices(X1,X2,X3)&r1_lattices(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_lattices)).
% 1.69/1.91  fof(commutativity_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 1.69/1.91  fof(c_0_17, plain, ![X21]:(v2_struct_0(X21)|~l1_lattices(X21)|m1_subset_1(k5_lattices(X21),u1_struct_0(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 1.69/1.91  fof(c_0_18, plain, ![X22]:((l1_lattices(X22)|~l3_lattices(X22))&(l2_lattices(X22)|~l3_lattices(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 1.69/1.91  fof(c_0_19, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 1.69/1.91  fof(c_0_20, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.69/1.91  cnf(c_0_21, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.69/1.91  cnf(c_0_22, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.69/1.91  fof(c_0_23, negated_conjecture, ((((~v2_struct_0(esk5_0)&v10_lattices(esk5_0))&v4_lattice3(esk5_0))&l3_lattices(esk5_0))&(v2_struct_0(esk5_0)|~v10_lattices(esk5_0)|~v13_lattices(esk5_0)|~l3_lattices(esk5_0)|k5_lattices(esk5_0)!=k15_lattice3(esk5_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 1.69/1.91  fof(c_0_24, plain, ![X40, X41]:(v2_struct_0(X40)|~l3_lattices(X40)|m1_subset_1(k15_lattice3(X40,X41),u1_struct_0(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 1.69/1.91  fof(c_0_25, plain, ![X8, X9]:~r2_hidden(X8,k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 1.69/1.91  cnf(c_0_26, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.69/1.91  fof(c_0_27, plain, ![X23, X24, X25]:(v2_struct_0(X23)|~v6_lattices(X23)|~l1_lattices(X23)|~m1_subset_1(X24,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X23))|k4_lattices(X23,X24,X25)=k2_lattices(X23,X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).
% 1.69/1.91  cnf(c_0_28, plain, (m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 1.69/1.91  cnf(c_0_29, negated_conjecture, (l3_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.69/1.91  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.69/1.91  cnf(c_0_31, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.69/1.91  fof(c_0_32, plain, ![X18, X19, X20]:(v2_struct_0(X18)|~v6_lattices(X18)|~l1_lattices(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|m1_subset_1(k4_lattices(X18,X19,X20),u1_struct_0(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).
% 1.69/1.91  cnf(c_0_33, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.69/1.91  cnf(c_0_34, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_26])).
% 1.69/1.91  fof(c_0_35, plain, ![X44, X45, X46, X48]:((m1_subset_1(esk4_3(X44,X45,X46),u1_struct_0(X44))|r3_lattices(X44,k15_lattice3(X44,X45),k15_lattice3(X44,X46))|(v2_struct_0(X44)|~v10_lattices(X44)|~v4_lattice3(X44)|~l3_lattices(X44)))&((r2_hidden(esk4_3(X44,X45,X46),X45)|r3_lattices(X44,k15_lattice3(X44,X45),k15_lattice3(X44,X46))|(v2_struct_0(X44)|~v10_lattices(X44)|~v4_lattice3(X44)|~l3_lattices(X44)))&(~m1_subset_1(X48,u1_struct_0(X44))|(~r3_lattices(X44,esk4_3(X44,X45,X46),X48)|~r2_hidden(X48,X46))|r3_lattices(X44,k15_lattice3(X44,X45),k15_lattice3(X44,X46))|(v2_struct_0(X44)|~v10_lattices(X44)|~v4_lattice3(X44)|~l3_lattices(X44))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).
% 1.69/1.91  fof(c_0_36, plain, ![X42, X43]:((X43=k15_lattice3(X42,a_2_3_lattice3(X42,X43))|~m1_subset_1(X43,u1_struct_0(X42))|(v2_struct_0(X42)|~v10_lattices(X42)|~v4_lattice3(X42)|~l3_lattices(X42)))&(X43=k16_lattice3(X42,a_2_4_lattice3(X42,X43))|~m1_subset_1(X43,u1_struct_0(X42))|(v2_struct_0(X42)|~v10_lattices(X42)|~v4_lattice3(X42)|~l3_lattices(X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).
% 1.69/1.91  cnf(c_0_37, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.69/1.91  cnf(c_0_38, negated_conjecture, (m1_subset_1(k5_lattices(esk5_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 1.69/1.91  fof(c_0_39, plain, ![X29, X30, X31]:(v2_struct_0(X29)|~v6_lattices(X29)|~v8_lattices(X29)|~l3_lattices(X29)|(~m1_subset_1(X30,u1_struct_0(X29))|(~m1_subset_1(X31,u1_struct_0(X29))|r1_lattices(X29,k4_lattices(X29,X30,X31),X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_lattices])])])])).
% 1.69/1.91  cnf(c_0_40, negated_conjecture, (m1_subset_1(k15_lattice3(esk5_0,X1),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_29]), c_0_30])).
% 1.69/1.91  cnf(c_0_41, plain, (v2_struct_0(X1)|m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.69/1.91  cnf(c_0_42, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.69/1.91  cnf(c_0_43, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.69/1.91  cnf(c_0_44, plain, (X1=k15_lattice3(X2,a_2_3_lattice3(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.69/1.91  cnf(c_0_45, negated_conjecture, (v4_lattice3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.69/1.91  cnf(c_0_46, negated_conjecture, (v10_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.69/1.91  cnf(c_0_47, negated_conjecture, (k4_lattices(esk5_0,X1,k5_lattices(esk5_0))=k2_lattices(esk5_0,X1,k5_lattices(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l1_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_30])).
% 1.69/1.91  fof(c_0_48, plain, ![X14, X15, X16]:(((k2_lattices(X14,X15,X16)=X15|~m1_subset_1(X16,u1_struct_0(X14))|X15!=k5_lattices(X14)|~m1_subset_1(X15,u1_struct_0(X14))|~v13_lattices(X14)|(v2_struct_0(X14)|~l1_lattices(X14)))&(k2_lattices(X14,X16,X15)=X15|~m1_subset_1(X16,u1_struct_0(X14))|X15!=k5_lattices(X14)|~m1_subset_1(X15,u1_struct_0(X14))|~v13_lattices(X14)|(v2_struct_0(X14)|~l1_lattices(X14))))&((m1_subset_1(esk1_2(X14,X15),u1_struct_0(X14))|X15=k5_lattices(X14)|~m1_subset_1(X15,u1_struct_0(X14))|~v13_lattices(X14)|(v2_struct_0(X14)|~l1_lattices(X14)))&(k2_lattices(X14,X15,esk1_2(X14,X15))!=X15|k2_lattices(X14,esk1_2(X14,X15),X15)!=X15|X15=k5_lattices(X14)|~m1_subset_1(X15,u1_struct_0(X14))|~v13_lattices(X14)|(v2_struct_0(X14)|~l1_lattices(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 1.69/1.91  cnf(c_0_49, plain, (v2_struct_0(X1)|r1_lattices(X1,k4_lattices(X1,X2,X3),X2)|~v6_lattices(X1)|~v8_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.69/1.91  cnf(c_0_50, negated_conjecture, (k4_lattices(esk5_0,X1,k15_lattice3(esk5_0,X2))=k2_lattices(esk5_0,X1,k15_lattice3(esk5_0,X2))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l1_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_40]), c_0_30])).
% 1.69/1.91  cnf(c_0_51, negated_conjecture, (m1_subset_1(k4_lattices(esk5_0,X1,k15_lattice3(esk5_0,X2)),u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l1_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_30])).
% 1.69/1.91  fof(c_0_52, plain, ![X26, X27, X28]:((~r3_lattices(X26,X27,X28)|r1_lattices(X26,X27,X28)|(v2_struct_0(X26)|~v6_lattices(X26)|~v8_lattices(X26)|~v9_lattices(X26)|~l3_lattices(X26)|~m1_subset_1(X27,u1_struct_0(X26))|~m1_subset_1(X28,u1_struct_0(X26))))&(~r1_lattices(X26,X27,X28)|r3_lattices(X26,X27,X28)|(v2_struct_0(X26)|~v6_lattices(X26)|~v8_lattices(X26)|~v9_lattices(X26)|~l3_lattices(X26)|~m1_subset_1(X27,u1_struct_0(X26))|~m1_subset_1(X28,u1_struct_0(X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 1.69/1.91  cnf(c_0_53, plain, (r3_lattices(X1,k15_lattice3(X1,k1_xboole_0),k15_lattice3(X1,X2))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.69/1.91  cnf(c_0_54, negated_conjecture, (k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,k5_lattices(esk5_0)))=k5_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_38]), c_0_45]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_55, negated_conjecture, (k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0))=k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0))|~l1_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(spm,[status(thm)],[c_0_47, c_0_40])).
% 1.69/1.91  fof(c_0_56, plain, ![X10]:(((((((~v2_struct_0(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10))&(v4_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v5_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v6_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v7_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v8_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v9_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 1.69/1.91  cnf(c_0_57, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.69/1.91  fof(c_0_58, plain, ![X35, X37, X38]:(((m1_subset_1(esk2_1(X35),u1_struct_0(X35))|~v13_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))&((k2_lattices(X35,esk2_1(X35),X37)=esk2_1(X35)|~m1_subset_1(X37,u1_struct_0(X35))|~v13_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))&(k2_lattices(X35,X37,esk2_1(X35))=esk2_1(X35)|~m1_subset_1(X37,u1_struct_0(X35))|~v13_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))))&((m1_subset_1(esk3_2(X35,X38),u1_struct_0(X35))|~m1_subset_1(X38,u1_struct_0(X35))|v13_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))&(k2_lattices(X35,X38,esk3_2(X35,X38))!=X38|k2_lattices(X35,esk3_2(X35,X38),X38)!=X38|~m1_subset_1(X38,u1_struct_0(X35))|v13_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 1.69/1.91  cnf(c_0_59, negated_conjecture, (r1_lattices(esk5_0,k4_lattices(esk5_0,X1,k15_lattice3(esk5_0,X2)),X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_40]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_60, negated_conjecture, (k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))=k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))|~l1_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(spm,[status(thm)],[c_0_50, c_0_40])).
% 1.69/1.91  cnf(c_0_61, negated_conjecture, (m1_subset_1(k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)),u1_struct_0(esk5_0))|~l1_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_40])).
% 1.69/1.91  cnf(c_0_62, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.69/1.91  cnf(c_0_63, negated_conjecture, (r3_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k5_lattices(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_45]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_64, negated_conjecture, (k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0))=k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0))|~v6_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_22]), c_0_29])])).
% 1.69/1.91  cnf(c_0_65, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 1.69/1.91  cnf(c_0_66, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~v13_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_57]), c_0_21])).
% 1.69/1.91  cnf(c_0_67, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.69/1.91  cnf(c_0_68, negated_conjecture, (r1_lattices(esk5_0,k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X1))|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(spm,[status(thm)],[c_0_59, c_0_40])).
% 1.69/1.91  cnf(c_0_69, negated_conjecture, (k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))=k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))|~v6_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_22]), c_0_29])])).
% 1.69/1.91  cnf(c_0_70, negated_conjecture, (m1_subset_1(k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)),u1_struct_0(esk5_0))|~v6_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_22]), c_0_29])])).
% 1.69/1.91  cnf(c_0_71, negated_conjecture, (r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k5_lattices(esk5_0))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_38]), c_0_40]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_72, negated_conjecture, (r1_lattices(esk5_0,k4_lattices(esk5_0,X1,k5_lattices(esk5_0)),X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_38]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_73, negated_conjecture, (k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0))=k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_74, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0))=k5_lattices(esk5_0)|~v13_lattices(esk5_0)|~l1_lattices(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_40]), c_0_30])).
% 1.69/1.91  cnf(c_0_75, negated_conjecture, (v13_lattices(esk5_0)|m1_subset_1(esk3_2(esk5_0,k15_lattice3(esk5_0,X1)),u1_struct_0(esk5_0))|~l1_lattices(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_40]), c_0_30])).
% 1.69/1.91  cnf(c_0_76, negated_conjecture, (r1_lattices(esk5_0,k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X1))|~v8_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_65]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_77, negated_conjecture, (k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))=k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_65]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_78, negated_conjecture, (m1_subset_1(k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_65]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_79, negated_conjecture, (r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k5_lattices(esk5_0))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_65]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_80, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 1.69/1.91  cnf(c_0_81, negated_conjecture, (r1_lattices(esk5_0,k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)),k15_lattice3(esk5_0,X1))|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_40]), c_0_73])).
% 1.69/1.91  cnf(c_0_82, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0))=k5_lattices(esk5_0)|~v13_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_22]), c_0_29])])).
% 1.69/1.91  cnf(c_0_83, negated_conjecture, (v13_lattices(esk5_0)|m1_subset_1(esk3_2(esk5_0,k15_lattice3(esk5_0,X1)),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_22]), c_0_29])])).
% 1.69/1.91  fof(c_0_84, plain, ![X32, X33, X34]:(v2_struct_0(X32)|~v4_lattices(X32)|~l2_lattices(X32)|(~m1_subset_1(X33,u1_struct_0(X32))|(~m1_subset_1(X34,u1_struct_0(X32))|(~r1_lattices(X32,X33,X34)|~r1_lattices(X32,X34,X33)|X33=X34)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_lattices])])])])).
% 1.69/1.91  cnf(c_0_85, negated_conjecture, (r1_lattices(esk5_0,k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X1))|~v8_lattices(esk5_0)), inference(rw,[status(thm)],[c_0_76, c_0_77])).
% 1.69/1.91  cnf(c_0_86, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 1.69/1.91  cnf(c_0_87, negated_conjecture, (m1_subset_1(k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)),u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_78, c_0_77])).
% 1.69/1.91  cnf(c_0_88, negated_conjecture, (r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k5_lattices(esk5_0))|~v9_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_89, negated_conjecture, (r1_lattices(esk5_0,k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)),k15_lattice3(esk5_0,X1))|~v8_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_65]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_90, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0))=k5_lattices(esk5_0)|m1_subset_1(esk3_2(esk5_0,k15_lattice3(esk5_0,X2)),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 1.69/1.91  fof(c_0_91, plain, ![X11, X12, X13]:(v2_struct_0(X11)|~v6_lattices(X11)|~l1_lattices(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~m1_subset_1(X13,u1_struct_0(X11))|k4_lattices(X11,X12,X13)=k4_lattices(X11,X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).
% 1.69/1.91  cnf(c_0_92, negated_conjecture, (k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,k15_lattice3(esk5_0,X1)))=k15_lattice3(esk5_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_40]), c_0_45]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_93, negated_conjecture, (m1_subset_1(k4_lattices(esk5_0,X1,k5_lattices(esk5_0)),u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l1_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_38]), c_0_30])).
% 1.69/1.91  cnf(c_0_94, plain, (v2_struct_0(X1)|X2=X3|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattices(X1,X2,X3)|~r1_lattices(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 1.69/1.91  cnf(c_0_95, negated_conjecture, (r1_lattices(esk5_0,k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)),k15_lattice3(esk5_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_80]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_96, plain, (r1_lattices(X1,k15_lattice3(X1,k1_xboole_0),k15_lattice3(X1,X2))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_53]), c_0_65]), c_0_80]), c_0_86]), c_0_31]), c_0_31])).
% 1.69/1.91  cnf(c_0_97, negated_conjecture, (k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))))=k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_87]), c_0_45]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_98, negated_conjecture, (r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k5_lattices(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_86]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_99, negated_conjecture, (r1_lattices(esk5_0,k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)),k15_lattice3(esk5_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_80]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_100, negated_conjecture, (k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,X1))))=esk3_2(esk5_0,k15_lattice3(esk5_0,X1))|k2_lattices(esk5_0,k15_lattice3(esk5_0,X2),k5_lattices(esk5_0))=k5_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_90]), c_0_45]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_101, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 1.69/1.91  cnf(c_0_102, negated_conjecture, (r3_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k15_lattice3(esk5_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_92]), c_0_45]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_103, negated_conjecture, (m1_subset_1(k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)),u1_struct_0(esk5_0))|~l1_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(spm,[status(thm)],[c_0_93, c_0_40])).
% 1.69/1.91  cnf(c_0_104, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))=k15_lattice3(esk5_0,X1)|~r1_lattices(esk5_0,k15_lattice3(esk5_0,X1),k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)))|~l2_lattices(esk5_0)|~v4_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_87]), c_0_40])]), c_0_30])).
% 1.69/1.91  cnf(c_0_105, negated_conjecture, (r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_45]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_106, negated_conjecture, (k5_lattices(esk5_0)=k15_lattice3(esk5_0,k1_xboole_0)|~r1_lattices(esk5_0,k5_lattices(esk5_0),k15_lattice3(esk5_0,k1_xboole_0))|~l2_lattices(esk5_0)|~v4_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_98]), c_0_40]), c_0_38])]), c_0_30])).
% 1.69/1.91  cnf(c_0_107, negated_conjecture, (k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,X1))))=esk3_2(esk5_0,k15_lattice3(esk5_0,X1))|r1_lattices(esk5_0,k5_lattices(esk5_0),k15_lattice3(esk5_0,X2))), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 1.69/1.91  cnf(c_0_108, negated_conjecture, (k4_lattices(esk5_0,X1,k15_lattice3(esk5_0,X2))=k4_lattices(esk5_0,k15_lattice3(esk5_0,X2),X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l1_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_40]), c_0_30])).
% 1.69/1.91  cnf(c_0_109, negated_conjecture, (r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k15_lattice3(esk5_0,X1))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_102]), c_0_40]), c_0_40]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_110, negated_conjecture, (m1_subset_1(k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)),u1_struct_0(esk5_0))|~v6_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_22]), c_0_29])])).
% 1.69/1.91  cnf(c_0_111, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k15_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,k1_xboole_0)|~l2_lattices(esk5_0)|~v4_lattices(esk5_0)), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 1.69/1.91  cnf(c_0_112, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.69/1.91  cnf(c_0_113, negated_conjecture, (k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,X1))))=esk3_2(esk5_0,k15_lattice3(esk5_0,X1))|k5_lattices(esk5_0)=k15_lattice3(esk5_0,k1_xboole_0)|~l2_lattices(esk5_0)|~v4_lattices(esk5_0)), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 1.69/1.91  cnf(c_0_114, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))=k2_lattices(esk5_0,k15_lattice3(esk5_0,X2),k15_lattice3(esk5_0,X1))|~l1_lattices(esk5_0)|~v6_lattices(esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_40]), c_0_77]), c_0_77])).
% 1.69/1.91  cnf(c_0_115, negated_conjecture, (r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k15_lattice3(esk5_0,X1))|~v9_lattices(esk5_0)|~v8_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_65]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_116, negated_conjecture, (m1_subset_1(k4_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_65]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_117, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k15_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,k1_xboole_0)|~v4_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_29])])).
% 1.69/1.91  cnf(c_0_118, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 1.69/1.91  cnf(c_0_119, negated_conjecture, (k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,X1))))=esk3_2(esk5_0,k15_lattice3(esk5_0,X1))|k5_lattices(esk5_0)=k15_lattice3(esk5_0,k1_xboole_0)|~v4_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_112]), c_0_29])])).
% 1.69/1.91  cnf(c_0_120, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))=k2_lattices(esk5_0,k15_lattice3(esk5_0,X2),k15_lattice3(esk5_0,X1))|~v6_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_22]), c_0_29])])).
% 1.69/1.91  cnf(c_0_121, negated_conjecture, (r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k15_lattice3(esk5_0,X1))|~v9_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_80]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_122, negated_conjecture, (m1_subset_1(k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)),u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_116, c_0_73])).
% 1.69/1.91  cnf(c_0_123, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k15_lattice3(esk5_0,X1))=k15_lattice3(esk5_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_124, negated_conjecture, (k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,X1))))=esk3_2(esk5_0,k15_lattice3(esk5_0,X1))|k5_lattices(esk5_0)=k15_lattice3(esk5_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_118]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_125, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,X2))=k2_lattices(esk5_0,k15_lattice3(esk5_0,X2),k15_lattice3(esk5_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_65]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_126, negated_conjecture, (r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k15_lattice3(esk5_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_86]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_127, negated_conjecture, (k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0))))=k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_122]), c_0_45]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_128, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|k2_lattices(X1,esk3_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.69/1.91  cnf(c_0_129, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),esk3_2(esk5_0,k15_lattice3(esk5_0,X1)))=k15_lattice3(esk5_0,k1_xboole_0)|k5_lattices(esk5_0)=k15_lattice3(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_123, c_0_124])).
% 1.69/1.91  cnf(c_0_130, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k15_lattice3(esk5_0,k1_xboole_0))=k15_lattice3(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_125, c_0_123])).
% 1.69/1.91  cnf(c_0_131, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0))=k15_lattice3(esk5_0,X1)|~r1_lattices(esk5_0,k15_lattice3(esk5_0,X1),k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)))|~l2_lattices(esk5_0)|~v4_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_99]), c_0_122]), c_0_40])]), c_0_30])).
% 1.69/1.91  cnf(c_0_132, negated_conjecture, (r1_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0)))), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 1.69/1.91  cnf(c_0_133, negated_conjecture, (k5_lattices(esk5_0)=k15_lattice3(esk5_0,k1_xboole_0)|v13_lattices(esk5_0)|k2_lattices(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,k1_xboole_0)),k15_lattice3(esk5_0,k1_xboole_0))!=k15_lattice3(esk5_0,k1_xboole_0)|~l1_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_40])]), c_0_30])).
% 1.69/1.91  cnf(c_0_134, negated_conjecture, (k2_lattices(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,X1)),k15_lattice3(esk5_0,k1_xboole_0))=k15_lattice3(esk5_0,k1_xboole_0)|k5_lattices(esk5_0)=k15_lattice3(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_130, c_0_124])).
% 1.69/1.91  cnf(c_0_135, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k5_lattices(esk5_0))=k15_lattice3(esk5_0,k1_xboole_0)|~l2_lattices(esk5_0)|~v4_lattices(esk5_0)), inference(spm,[status(thm)],[c_0_131, c_0_132])).
% 1.69/1.91  cnf(c_0_136, negated_conjecture, (k5_lattices(esk5_0)=k15_lattice3(esk5_0,k1_xboole_0)|v13_lattices(esk5_0)|~l1_lattices(esk5_0)), inference(spm,[status(thm)],[c_0_133, c_0_134])).
% 1.69/1.91  cnf(c_0_137, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k5_lattices(esk5_0))=k15_lattice3(esk5_0,k1_xboole_0)|~v4_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_112]), c_0_29])])).
% 1.69/1.91  cnf(c_0_138, negated_conjecture, (k5_lattices(esk5_0)=k15_lattice3(esk5_0,k1_xboole_0)|v13_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_22]), c_0_29])])).
% 1.69/1.91  cnf(c_0_139, negated_conjecture, (v2_struct_0(esk5_0)|~v10_lattices(esk5_0)|~v13_lattices(esk5_0)|~l3_lattices(esk5_0)|k5_lattices(esk5_0)!=k15_lattice3(esk5_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.69/1.91  cnf(c_0_140, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),k5_lattices(esk5_0))=k15_lattice3(esk5_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_118]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_141, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,X1),k5_lattices(esk5_0))=k5_lattices(esk5_0)|k5_lattices(esk5_0)=k15_lattice3(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_82, c_0_138])).
% 1.69/1.91  cnf(c_0_142, negated_conjecture, (k5_lattices(esk5_0)!=k15_lattice3(esk5_0,k1_xboole_0)|~v13_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139, c_0_29]), c_0_46])]), c_0_30])).
% 1.69/1.91  cnf(c_0_143, negated_conjecture, (k5_lattices(esk5_0)=k15_lattice3(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_140, c_0_141])).
% 1.69/1.91  cnf(c_0_144, negated_conjecture, (~v13_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_142, c_0_143])])).
% 1.69/1.91  cnf(c_0_145, negated_conjecture, (m1_subset_1(esk3_2(esk5_0,k15_lattice3(esk5_0,X1)),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[c_0_83, c_0_144])).
% 1.69/1.91  cnf(c_0_146, negated_conjecture, (k15_lattice3(esk5_0,a_2_3_lattice3(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,X1))))=esk3_2(esk5_0,k15_lattice3(esk5_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_145]), c_0_45]), c_0_46]), c_0_29])]), c_0_30])).
% 1.69/1.91  cnf(c_0_147, negated_conjecture, (k2_lattices(esk5_0,k15_lattice3(esk5_0,k1_xboole_0),esk3_2(esk5_0,k15_lattice3(esk5_0,X1)))=k15_lattice3(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_123, c_0_146])).
% 1.69/1.91  cnf(c_0_148, negated_conjecture, (k2_lattices(esk5_0,esk3_2(esk5_0,k15_lattice3(esk5_0,X1)),k15_lattice3(esk5_0,k1_xboole_0))=k15_lattice3(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_130, c_0_146])).
% 1.69/1.91  cnf(c_0_149, negated_conjecture, (~l1_lattices(esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_147]), c_0_148]), c_0_40])]), c_0_144]), c_0_30])).
% 1.69/1.91  cnf(c_0_150, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_22]), c_0_29])]), ['proof']).
% 1.69/1.91  # SZS output end CNFRefutation
% 1.69/1.91  # Proof object total steps             : 151
% 1.69/1.91  # Proof object clause steps            : 116
% 1.69/1.91  # Proof object formula steps           : 35
% 1.69/1.91  # Proof object conjectures             : 92
% 1.69/1.91  # Proof object clause conjectures      : 89
% 1.69/1.91  # Proof object formula conjectures     : 3
% 1.69/1.91  # Proof object initial clauses used    : 26
% 1.69/1.91  # Proof object initial formulas used   : 17
% 1.69/1.91  # Proof object generating inferences   : 82
% 1.69/1.91  # Proof object simplifying inferences  : 207
% 1.69/1.91  # Training examples: 0 positive, 0 negative
% 1.69/1.91  # Parsed axioms                        : 17
% 1.69/1.91  # Removed by relevancy pruning/SinE    : 0
% 1.69/1.91  # Initial clauses                      : 41
% 1.69/1.91  # Removed in clause preprocessing      : 1
% 1.69/1.91  # Initial clauses in saturation        : 40
% 1.69/1.91  # Processed clauses                    : 6399
% 1.69/1.91  # ...of these trivial                  : 117
% 1.69/1.91  # ...subsumed                          : 2222
% 1.69/1.91  # ...remaining for further processing  : 4060
% 1.69/1.91  # Other redundant clauses eliminated   : 4
% 1.69/1.91  # Clauses deleted for lack of memory   : 0
% 1.69/1.91  # Backward-subsumed                    : 1443
% 1.69/1.91  # Backward-rewritten                   : 2358
% 1.69/1.91  # Generated clauses                    : 150672
% 1.69/1.91  # ...of the previous two non-trivial   : 150867
% 1.69/1.91  # Contextual simplify-reflections      : 235
% 1.69/1.91  # Paramodulations                      : 150657
% 1.69/1.91  # Factorizations                       : 1
% 1.69/1.91  # Equation resolutions                 : 4
% 1.69/1.91  # Propositional unsat checks           : 0
% 1.69/1.91  #    Propositional check models        : 0
% 1.69/1.91  #    Propositional check unsatisfiable : 0
% 1.69/1.91  #    Propositional clauses             : 0
% 1.69/1.91  #    Propositional clauses after purity: 0
% 1.69/1.91  #    Propositional unsat core size     : 0
% 1.69/1.91  #    Propositional preprocessing time  : 0.000
% 1.69/1.91  #    Propositional encoding time       : 0.000
% 1.69/1.91  #    Propositional solver time         : 0.000
% 1.69/1.91  #    Success case prop preproc time    : 0.000
% 1.69/1.91  #    Success case prop encoding time   : 0.000
% 1.69/1.91  #    Success case prop solver time     : 0.000
% 1.69/1.91  # Current number of processed clauses  : 205
% 1.69/1.91  #    Positive orientable unit clauses  : 32
% 1.69/1.91  #    Positive unorientable unit clauses: 1
% 1.69/1.91  #    Negative unit clauses             : 5
% 1.69/1.91  #    Non-unit-clauses                  : 167
% 1.69/1.91  # Current number of unprocessed clauses: 144222
% 1.69/1.91  # ...number of literals in the above   : 547667
% 1.69/1.91  # Current number of archived formulas  : 0
% 1.69/1.91  # Current number of archived clauses   : 3851
% 1.69/1.91  # Clause-clause subsumption calls (NU) : 1418971
% 1.69/1.91  # Rec. Clause-clause subsumption calls : 717110
% 1.69/1.91  # Non-unit clause-clause subsumptions  : 3673
% 1.69/1.91  # Unit Clause-clause subsumption calls : 6647
% 1.69/1.91  # Rewrite failures with RHS unbound    : 0
% 1.69/1.91  # BW rewrite match attempts            : 1382
% 1.69/1.91  # BW rewrite match successes           : 83
% 1.69/1.91  # Condensation attempts                : 0
% 1.69/1.91  # Condensation successes               : 0
% 1.69/1.91  # Termbank termtop insertions          : 4588559
% 1.77/1.92  
% 1.77/1.92  # -------------------------------------------------
% 1.77/1.92  # User time                : 1.539 s
% 1.77/1.92  # System time              : 0.052 s
% 1.77/1.92  # Total time               : 1.590 s
% 1.77/1.92  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
