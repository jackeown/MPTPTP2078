%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:09 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  131 (97224 expanded)
%              Number of clauses        :  102 (34387 expanded)
%              Number of leaves         :   14 (23571 expanded)
%              Depth                    :   24
%              Number of atoms          :  536 (637960 expanded)
%              Number of equality atoms :  132 (63415 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   28 (   2 average)
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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

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

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

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

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

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

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_16,plain,(
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

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v10_lattices(esk7_0)
    & v4_lattice3(esk7_0)
    & l3_lattices(esk7_0)
    & ( v2_struct_0(esk7_0)
      | ~ v10_lattices(esk7_0)
      | ~ v13_lattices(esk7_0)
      | ~ l3_lattices(esk7_0)
      | k5_lattices(esk7_0) != k15_lattice3(esk7_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_18,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_19,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X37,X38,X39,X41] :
      ( ( m1_subset_1(esk6_3(X37,X38,X39),u1_struct_0(X37))
        | r3_lattices(X37,k15_lattice3(X37,X38),k15_lattice3(X37,X39))
        | v2_struct_0(X37)
        | ~ v10_lattices(X37)
        | ~ v4_lattice3(X37)
        | ~ l3_lattices(X37) )
      & ( r2_hidden(esk6_3(X37,X38,X39),X38)
        | r3_lattices(X37,k15_lattice3(X37,X38),k15_lattice3(X37,X39))
        | v2_struct_0(X37)
        | ~ v10_lattices(X37)
        | ~ v4_lattice3(X37)
        | ~ l3_lattices(X37) )
      & ( ~ m1_subset_1(X41,u1_struct_0(X37))
        | ~ r3_lattices(X37,esk6_3(X37,X38,X39),X41)
        | ~ r2_hidden(X41,X39)
        | r3_lattices(X37,k15_lattice3(X37,X38),k15_lattice3(X37,X39))
        | v2_struct_0(X37)
        | ~ v10_lattices(X37)
        | ~ v4_lattice3(X37)
        | ~ l3_lattices(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).

fof(c_0_21,plain,(
    ! [X16] :
      ( ( l1_lattices(X16)
        | ~ l3_lattices(X16) )
      & ( l2_lattices(X16)
        | ~ l3_lattices(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_22,plain,(
    ! [X17,X18,X19] :
      ( ( ~ r3_lattices(X17,X18,X19)
        | r1_lattices(X17,X18,X19)
        | v2_struct_0(X17)
        | ~ v6_lattices(X17)
        | ~ v8_lattices(X17)
        | ~ v9_lattices(X17)
        | ~ l3_lattices(X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17)) )
      & ( ~ r1_lattices(X17,X18,X19)
        | r3_lattices(X17,X18,X19)
        | v2_struct_0(X17)
        | ~ v6_lattices(X17)
        | ~ v8_lattices(X17)
        | ~ v9_lattices(X17)
        | ~ l3_lattices(X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_23,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v10_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( l3_lattices(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( v4_lattice3(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_33,plain,(
    ! [X33,X34] :
      ( v2_struct_0(X33)
      | ~ l3_lattices(X33)
      | m1_subset_1(k15_lattice3(X33,X34),u1_struct_0(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_34,plain,(
    ! [X28,X29,X30] :
      ( ( ~ v6_lattices(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | k2_lattices(X28,X29,X30) = k2_lattices(X28,X30,X29)
        | v2_struct_0(X28)
        | ~ l1_lattices(X28) )
      & ( m1_subset_1(esk4_1(X28),u1_struct_0(X28))
        | v6_lattices(X28)
        | v2_struct_0(X28)
        | ~ l1_lattices(X28) )
      & ( m1_subset_1(esk5_1(X28),u1_struct_0(X28))
        | v6_lattices(X28)
        | v2_struct_0(X28)
        | ~ l1_lattices(X28) )
      & ( k2_lattices(X28,esk4_1(X28),esk5_1(X28)) != k2_lattices(X28,esk5_1(X28),esk4_1(X28))
        | v6_lattices(X28)
        | v2_struct_0(X28)
        | ~ l1_lattices(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

cnf(c_0_35,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_36,plain,(
    ! [X23,X25,X26] :
      ( ( m1_subset_1(esk2_1(X23),u1_struct_0(X23))
        | ~ v13_lattices(X23)
        | v2_struct_0(X23)
        | ~ l1_lattices(X23) )
      & ( k2_lattices(X23,esk2_1(X23),X25) = esk2_1(X23)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ v13_lattices(X23)
        | v2_struct_0(X23)
        | ~ l1_lattices(X23) )
      & ( k2_lattices(X23,X25,esk2_1(X23)) = esk2_1(X23)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ v13_lattices(X23)
        | v2_struct_0(X23)
        | ~ l1_lattices(X23) )
      & ( m1_subset_1(esk3_2(X23,X26),u1_struct_0(X23))
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | v13_lattices(X23)
        | v2_struct_0(X23)
        | ~ l1_lattices(X23) )
      & ( k2_lattices(X23,X26,esk3_2(X23,X26)) != X26
        | k2_lattices(X23,esk3_2(X23,X26),X26) != X26
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | v13_lattices(X23)
        | v2_struct_0(X23)
        | ~ l1_lattices(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

fof(c_0_37,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r1_lattices(X20,X21,X22)
        | k2_lattices(X20,X21,X22) = X21
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v8_lattices(X20)
        | ~ v9_lattices(X20)
        | ~ l3_lattices(X20) )
      & ( k2_lattices(X20,X21,X22) != X21
        | r1_lattices(X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v8_lattices(X20)
        | ~ v9_lattices(X20)
        | ~ l3_lattices(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_38,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( v9_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( v8_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( v6_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( r3_lattices(esk7_0,k15_lattice3(esk7_0,X1),k15_lattice3(esk7_0,X2))
    | r2_hidden(esk6_3(esk7_0,X1,X2),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( l1_lattices(esk7_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_25])).

fof(c_0_47,plain,(
    ! [X15] :
      ( v2_struct_0(X15)
      | ~ l1_lattices(X15)
      | m1_subset_1(k5_lattices(X15),u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_48,plain,(
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

cnf(c_0_49,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( r1_lattices(esk7_0,X1,X2)
    | ~ r3_lattices(esk7_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_25])]),c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( r3_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k15_lattice3(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk7_0,X1),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_25]),c_0_26])).

cnf(c_0_54,negated_conjecture,
    ( k2_lattices(esk7_0,X1,X2) = k2_lattices(esk7_0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_41])]),c_0_26])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk3_2(esk7_0,X1),u1_struct_0(esk7_0))
    | v13_lattices(esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_46]),c_0_26])).

cnf(c_0_58,negated_conjecture,
    ( k2_lattices(esk7_0,X1,X2) = X1
    | ~ r1_lattices(esk7_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_39]),c_0_40]),c_0_25])]),c_0_26])).

cnf(c_0_59,negated_conjecture,
    ( r1_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k15_lattice3(esk7_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_53])])).

cnf(c_0_60,negated_conjecture,
    ( k2_lattices(esk7_0,X1,k15_lattice3(esk7_0,X2)) = k2_lattices(esk7_0,k15_lattice3(esk7_0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_53])).

fof(c_0_61,plain,(
    ! [X35,X36] :
      ( ( X36 = k15_lattice3(X35,a_2_3_lattice3(X35,X36))
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) )
      & ( X36 = k16_lattice3(X35,a_2_4_lattice3(X35,X36))
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ v10_lattices(X35)
        | ~ v4_lattice3(X35)
        | ~ l3_lattices(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk7_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_46]),c_0_26])).

cnf(c_0_63,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_56]),c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),u1_struct_0(esk7_0))
    | v13_lattices(esk7_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k15_lattice3(esk7_0,X1)) = k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_53]),c_0_53])])).

cnf(c_0_66,negated_conjecture,
    ( k2_lattices(esk7_0,k15_lattice3(esk7_0,X1),k15_lattice3(esk7_0,X2)) = k2_lattices(esk7_0,k15_lattice3(esk7_0,X2),k15_lattice3(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_53])).

cnf(c_0_67,plain,
    ( X1 = k15_lattice3(X2,a_2_3_lattice3(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_68,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X3) != X2
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_69,negated_conjecture,
    ( k2_lattices(esk7_0,X1,k5_lattices(esk7_0)) = k2_lattices(esk7_0,k5_lattices(esk7_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( k2_lattices(esk7_0,X1,k5_lattices(esk7_0)) = k5_lattices(esk7_0)
    | m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,X2)),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_46])]),c_0_26])).

cnf(c_0_71,plain,
    ( m1_subset_1(esk2_1(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_72,negated_conjecture,
    ( k2_lattices(esk7_0,k15_lattice3(esk7_0,X1),k15_lattice3(esk7_0,k1_xboole_0)) = k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,X1)) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_32]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_74,negated_conjecture,
    ( r1_lattices(esk7_0,X1,X2)
    | k2_lattices(esk7_0,X1,X2) != X1
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_39]),c_0_40]),c_0_25])]),c_0_26])).

cnf(c_0_75,negated_conjecture,
    ( k2_lattices(esk7_0,k15_lattice3(esk7_0,X1),k5_lattices(esk7_0)) = k2_lattices(esk7_0,k5_lattices(esk7_0),k15_lattice3(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_53])).

cnf(c_0_76,negated_conjecture,
    ( k2_lattices(esk7_0,k15_lattice3(esk7_0,X1),k5_lattices(esk7_0)) = k5_lattices(esk7_0)
    | m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,X2)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_53])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),u1_struct_0(esk7_0))
    | m1_subset_1(esk2_1(esk7_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_64]),c_0_46])]),c_0_26])).

cnf(c_0_78,negated_conjecture,
    ( k15_lattice3(esk7_0,k1_xboole_0) = k15_lattice3(esk7_0,X1)
    | ~ r1_lattices(esk7_0,k15_lattice3(esk7_0,X1),k15_lattice3(esk7_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_72]),c_0_53]),c_0_53])])).

cnf(c_0_79,negated_conjecture,
    ( k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,k5_lattices(esk7_0))) = k5_lattices(esk7_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_62])).

cnf(c_0_80,negated_conjecture,
    ( r1_lattices(esk7_0,k5_lattices(esk7_0),k15_lattice3(esk7_0,X1))
    | k2_lattices(esk7_0,k15_lattice3(esk7_0,X1),k5_lattices(esk7_0)) != k5_lattices(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_53]),c_0_62])])).

cnf(c_0_81,negated_conjecture,
    ( k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1)))) = esk3_2(esk7_0,k15_lattice3(esk7_0,X1))
    | k2_lattices(esk7_0,k15_lattice3(esk7_0,X2),k5_lattices(esk7_0)) = k5_lattices(esk7_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_76])).

cnf(c_0_82,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | k2_lattices(X1,esk3_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_83,negated_conjecture,
    ( k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1)))) = esk3_2(esk7_0,k15_lattice3(esk7_0,X1))
    | m1_subset_1(esk2_1(esk7_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( k5_lattices(esk7_0) = k15_lattice3(esk7_0,k1_xboole_0)
    | ~ r1_lattices(esk7_0,k5_lattices(esk7_0),k15_lattice3(esk7_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1)))) = esk3_2(esk7_0,k15_lattice3(esk7_0,X1))
    | r1_lattices(esk7_0,k5_lattices(esk7_0),k15_lattice3(esk7_0,X2)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( v13_lattices(esk7_0)
    | k2_lattices(esk7_0,X1,esk3_2(esk7_0,X1)) != X1
    | k2_lattices(esk7_0,esk3_2(esk7_0,X1),X1) != X1
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_46]),c_0_26])).

cnf(c_0_87,negated_conjecture,
    ( k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1)))) = esk3_2(esk7_0,k15_lattice3(esk7_0,X1))
    | k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk2_1(esk7_0))) = esk2_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1)))) = esk3_2(esk7_0,k15_lattice3(esk7_0,X1))
    | k5_lattices(esk7_0) = k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( v13_lattices(esk7_0)
    | k2_lattices(esk7_0,k15_lattice3(esk7_0,X1),esk3_2(esk7_0,k15_lattice3(esk7_0,X1))) != k15_lattice3(esk7_0,X1)
    | k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),k15_lattice3(esk7_0,X1)) != k15_lattice3(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_53])).

cnf(c_0_90,negated_conjecture,
    ( k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),esk3_2(esk7_0,k15_lattice3(esk7_0,X1))) = k15_lattice3(esk7_0,k1_xboole_0)
    | k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk2_1(esk7_0))) = esk2_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),esk3_2(esk7_0,k15_lattice3(esk7_0,X1))) = k15_lattice3(esk7_0,k1_xboole_0)
    | k5_lattices(esk7_0) = k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk2_1(esk7_0))) = esk2_1(esk7_0)
    | v13_lattices(esk7_0)
    | k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0)),k15_lattice3(esk7_0,k1_xboole_0)) != k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),k15_lattice3(esk7_0,k1_xboole_0)) = k15_lattice3(esk7_0,k1_xboole_0)
    | k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk2_1(esk7_0))) = esk2_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( k5_lattices(esk7_0) = k15_lattice3(esk7_0,k1_xboole_0)
    | v13_lattices(esk7_0)
    | k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0)),k15_lattice3(esk7_0,k1_xboole_0)) != k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),k15_lattice3(esk7_0,k1_xboole_0)) = k15_lattice3(esk7_0,k1_xboole_0)
    | k5_lattices(esk7_0) = k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_88])).

cnf(c_0_96,plain,
    ( k2_lattices(X1,X2,esk2_1(X1)) = esk2_1(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_97,negated_conjecture,
    ( k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk2_1(esk7_0))) = esk2_1(esk7_0)
    | v13_lattices(esk7_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( k5_lattices(esk7_0) = k15_lattice3(esk7_0,k1_xboole_0)
    | v13_lattices(esk7_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( k2_lattices(esk7_0,X1,esk2_1(esk7_0)) = esk2_1(esk7_0)
    | m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,X2)),u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_64]),c_0_46])]),c_0_26])).

cnf(c_0_100,negated_conjecture,
    ( k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk2_1(esk7_0))) = esk2_1(esk7_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_97]),c_0_46])]),c_0_26]),c_0_73])).

cnf(c_0_101,negated_conjecture,
    ( k2_lattices(esk7_0,X1,esk2_1(esk7_0)) = esk2_1(esk7_0)
    | k5_lattices(esk7_0) = k15_lattice3(esk7_0,k1_xboole_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_98]),c_0_46])]),c_0_26])).

cnf(c_0_102,negated_conjecture,
    ( r3_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k5_lattices(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_79])).

cnf(c_0_103,negated_conjecture,
    ( k2_lattices(esk7_0,k5_lattices(esk7_0),esk2_1(esk7_0)) = esk2_1(esk7_0)
    | m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_62])).

cnf(c_0_104,negated_conjecture,
    ( k2_lattices(esk7_0,X1,k5_lattices(esk7_0)) = k5_lattices(esk7_0)
    | k5_lattices(esk7_0) = k15_lattice3(esk7_0,k1_xboole_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_98]),c_0_46])]),c_0_26])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(esk2_1(esk7_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_100]),c_0_25])]),c_0_26])).

cnf(c_0_106,negated_conjecture,
    ( k2_lattices(esk7_0,esk2_1(esk7_0),k5_lattices(esk7_0)) = k2_lattices(esk7_0,k5_lattices(esk7_0),esk2_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),esk2_1(esk7_0)) = k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_100])).

cnf(c_0_108,negated_conjecture,
    ( k2_lattices(esk7_0,k15_lattice3(esk7_0,X1),esk2_1(esk7_0)) = esk2_1(esk7_0)
    | k5_lattices(esk7_0) = k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_53])).

cnf(c_0_109,negated_conjecture,
    ( r1_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k5_lattices(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_102]),c_0_62]),c_0_53])])).

cnf(c_0_110,negated_conjecture,
    ( k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1)))) = esk3_2(esk7_0,k15_lattice3(esk7_0,X1))
    | k2_lattices(esk7_0,k5_lattices(esk7_0),esk2_1(esk7_0)) = esk2_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_103])).

cnf(c_0_111,negated_conjecture,
    ( v2_struct_0(esk7_0)
    | ~ v10_lattices(esk7_0)
    | ~ v13_lattices(esk7_0)
    | ~ l3_lattices(esk7_0)
    | k5_lattices(esk7_0) != k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_112,negated_conjecture,
    ( k2_lattices(esk7_0,k5_lattices(esk7_0),esk2_1(esk7_0)) = k5_lattices(esk7_0)
    | k5_lattices(esk7_0) = k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_106])).

cnf(c_0_113,negated_conjecture,
    ( k5_lattices(esk7_0) = k15_lattice3(esk7_0,k1_xboole_0)
    | esk2_1(esk7_0) = k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_114,negated_conjecture,
    ( k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k5_lattices(esk7_0)) = k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_109]),c_0_62]),c_0_53])])).

cnf(c_0_115,negated_conjecture,
    ( k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),esk3_2(esk7_0,k15_lattice3(esk7_0,X1))) = k15_lattice3(esk7_0,k1_xboole_0)
    | k2_lattices(esk7_0,k5_lattices(esk7_0),esk2_1(esk7_0)) = esk2_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_110])).

cnf(c_0_116,negated_conjecture,
    ( k5_lattices(esk7_0) != k15_lattice3(esk7_0,k1_xboole_0)
    | ~ v13_lattices(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_25]),c_0_24])]),c_0_26])).

cnf(c_0_117,negated_conjecture,
    ( k5_lattices(esk7_0) = k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_75]),c_0_114])])).

cnf(c_0_118,negated_conjecture,
    ( k2_lattices(esk7_0,k5_lattices(esk7_0),esk2_1(esk7_0)) = esk2_1(esk7_0)
    | v13_lattices(esk7_0)
    | k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0)),k15_lattice3(esk7_0,k1_xboole_0)) != k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_115])).

cnf(c_0_119,negated_conjecture,
    ( k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),k15_lattice3(esk7_0,k1_xboole_0)) = k15_lattice3(esk7_0,k1_xboole_0)
    | k2_lattices(esk7_0,k5_lattices(esk7_0),esk2_1(esk7_0)) = esk2_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_110])).

cnf(c_0_120,negated_conjecture,
    ( ~ v13_lattices(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_117])])).

cnf(c_0_121,negated_conjecture,
    ( k2_lattices(esk7_0,k5_lattices(esk7_0),esk2_1(esk7_0)) = esk2_1(esk7_0)
    | v13_lattices(esk7_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_122,negated_conjecture,
    ( m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[c_0_64,c_0_120])).

cnf(c_0_123,negated_conjecture,
    ( v13_lattices(esk7_0)
    | k2_lattices(esk7_0,esk2_1(esk7_0),esk3_2(esk7_0,esk2_1(esk7_0))) != esk2_1(esk7_0)
    | k2_lattices(esk7_0,esk3_2(esk7_0,esk2_1(esk7_0)),esk2_1(esk7_0)) != esk2_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_100])).

cnf(c_0_124,negated_conjecture,
    ( esk2_1(esk7_0) = k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_117]),c_0_107]),c_0_120])).

cnf(c_0_125,negated_conjecture,
    ( k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1)))) = esk3_2(esk7_0,k15_lattice3(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_122])).

cnf(c_0_126,negated_conjecture,
    ( k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),esk3_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0))) != k15_lattice3(esk7_0,k1_xboole_0)
    | k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0)),k15_lattice3(esk7_0,k1_xboole_0)) != k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_124]),c_0_124]),c_0_124]),c_0_124]),c_0_124]),c_0_124]),c_0_120])).

cnf(c_0_127,negated_conjecture,
    ( k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),esk3_2(esk7_0,k15_lattice3(esk7_0,X1))) = k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_125])).

cnf(c_0_128,negated_conjecture,
    ( k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0)),k15_lattice3(esk7_0,k1_xboole_0)) != k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_127])])).

cnf(c_0_129,negated_conjecture,
    ( k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),k15_lattice3(esk7_0,k1_xboole_0)) = k15_lattice3(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_125])).

cnf(c_0_130,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_129])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:13:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.48/0.65  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 0.48/0.65  # and selection function HSelectMinInfpos.
% 0.48/0.65  #
% 0.48/0.65  # Preprocessing time       : 0.030 s
% 0.48/0.65  # Presaturation interreduction done
% 0.48/0.65  
% 0.48/0.65  # Proof found!
% 0.48/0.65  # SZS status Theorem
% 0.48/0.65  # SZS output start CNFRefutation
% 0.48/0.65  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_lattice3)).
% 0.48/0.65  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.48/0.65  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.48/0.65  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.48/0.65  fof(t48_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_lattice3)).
% 0.48/0.65  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.48/0.65  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.48/0.65  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.48/0.65  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_lattices)).
% 0.48/0.65  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_lattices)).
% 0.48/0.65  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 0.48/0.65  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.48/0.65  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 0.48/0.65  fof(t45_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k15_lattice3(X1,a_2_3_lattice3(X1,X2))&X2=k16_lattice3(X1,a_2_4_lattice3(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_lattice3)).
% 0.48/0.65  fof(c_0_14, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 0.48/0.65  fof(c_0_15, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.48/0.65  fof(c_0_16, plain, ![X10]:(((((((~v2_struct_0(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10))&(v4_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v5_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v6_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v7_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v8_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10)))&(v9_lattices(X10)|(v2_struct_0(X10)|~v10_lattices(X10))|~l3_lattices(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.48/0.65  fof(c_0_17, negated_conjecture, ((((~v2_struct_0(esk7_0)&v10_lattices(esk7_0))&v4_lattice3(esk7_0))&l3_lattices(esk7_0))&(v2_struct_0(esk7_0)|~v10_lattices(esk7_0)|~v13_lattices(esk7_0)|~l3_lattices(esk7_0)|k5_lattices(esk7_0)!=k15_lattice3(esk7_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.48/0.65  fof(c_0_18, plain, ![X8, X9]:~r2_hidden(X8,k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.48/0.65  cnf(c_0_19, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.48/0.65  fof(c_0_20, plain, ![X37, X38, X39, X41]:((m1_subset_1(esk6_3(X37,X38,X39),u1_struct_0(X37))|r3_lattices(X37,k15_lattice3(X37,X38),k15_lattice3(X37,X39))|(v2_struct_0(X37)|~v10_lattices(X37)|~v4_lattice3(X37)|~l3_lattices(X37)))&((r2_hidden(esk6_3(X37,X38,X39),X38)|r3_lattices(X37,k15_lattice3(X37,X38),k15_lattice3(X37,X39))|(v2_struct_0(X37)|~v10_lattices(X37)|~v4_lattice3(X37)|~l3_lattices(X37)))&(~m1_subset_1(X41,u1_struct_0(X37))|(~r3_lattices(X37,esk6_3(X37,X38,X39),X41)|~r2_hidden(X41,X39))|r3_lattices(X37,k15_lattice3(X37,X38),k15_lattice3(X37,X39))|(v2_struct_0(X37)|~v10_lattices(X37)|~v4_lattice3(X37)|~l3_lattices(X37))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).
% 0.48/0.65  fof(c_0_21, plain, ![X16]:((l1_lattices(X16)|~l3_lattices(X16))&(l2_lattices(X16)|~l3_lattices(X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.48/0.65  fof(c_0_22, plain, ![X17, X18, X19]:((~r3_lattices(X17,X18,X19)|r1_lattices(X17,X18,X19)|(v2_struct_0(X17)|~v6_lattices(X17)|~v8_lattices(X17)|~v9_lattices(X17)|~l3_lattices(X17)|~m1_subset_1(X18,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))))&(~r1_lattices(X17,X18,X19)|r3_lattices(X17,X18,X19)|(v2_struct_0(X17)|~v6_lattices(X17)|~v8_lattices(X17)|~v9_lattices(X17)|~l3_lattices(X17)|~m1_subset_1(X18,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.48/0.65  cnf(c_0_23, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.48/0.65  cnf(c_0_24, negated_conjecture, (v10_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.48/0.65  cnf(c_0_25, negated_conjecture, (l3_lattices(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.48/0.65  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.48/0.65  cnf(c_0_27, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.48/0.65  cnf(c_0_28, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.48/0.65  cnf(c_0_29, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.48/0.65  cnf(c_0_30, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_19])).
% 0.48/0.65  cnf(c_0_31, plain, (r2_hidden(esk6_3(X1,X2,X3),X2)|r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.48/0.65  cnf(c_0_32, negated_conjecture, (v4_lattice3(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.48/0.65  fof(c_0_33, plain, ![X33, X34]:(v2_struct_0(X33)|~l3_lattices(X33)|m1_subset_1(k15_lattice3(X33,X34),u1_struct_0(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.48/0.65  fof(c_0_34, plain, ![X28, X29, X30]:((~v6_lattices(X28)|(~m1_subset_1(X29,u1_struct_0(X28))|(~m1_subset_1(X30,u1_struct_0(X28))|k2_lattices(X28,X29,X30)=k2_lattices(X28,X30,X29)))|(v2_struct_0(X28)|~l1_lattices(X28)))&((m1_subset_1(esk4_1(X28),u1_struct_0(X28))|v6_lattices(X28)|(v2_struct_0(X28)|~l1_lattices(X28)))&((m1_subset_1(esk5_1(X28),u1_struct_0(X28))|v6_lattices(X28)|(v2_struct_0(X28)|~l1_lattices(X28)))&(k2_lattices(X28,esk4_1(X28),esk5_1(X28))!=k2_lattices(X28,esk5_1(X28),esk4_1(X28))|v6_lattices(X28)|(v2_struct_0(X28)|~l1_lattices(X28)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 0.48/0.65  cnf(c_0_35, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.65  fof(c_0_36, plain, ![X23, X25, X26]:(((m1_subset_1(esk2_1(X23),u1_struct_0(X23))|~v13_lattices(X23)|(v2_struct_0(X23)|~l1_lattices(X23)))&((k2_lattices(X23,esk2_1(X23),X25)=esk2_1(X23)|~m1_subset_1(X25,u1_struct_0(X23))|~v13_lattices(X23)|(v2_struct_0(X23)|~l1_lattices(X23)))&(k2_lattices(X23,X25,esk2_1(X23))=esk2_1(X23)|~m1_subset_1(X25,u1_struct_0(X23))|~v13_lattices(X23)|(v2_struct_0(X23)|~l1_lattices(X23)))))&((m1_subset_1(esk3_2(X23,X26),u1_struct_0(X23))|~m1_subset_1(X26,u1_struct_0(X23))|v13_lattices(X23)|(v2_struct_0(X23)|~l1_lattices(X23)))&(k2_lattices(X23,X26,esk3_2(X23,X26))!=X26|k2_lattices(X23,esk3_2(X23,X26),X26)!=X26|~m1_subset_1(X26,u1_struct_0(X23))|v13_lattices(X23)|(v2_struct_0(X23)|~l1_lattices(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 0.48/0.65  fof(c_0_37, plain, ![X20, X21, X22]:((~r1_lattices(X20,X21,X22)|k2_lattices(X20,X21,X22)=X21|~m1_subset_1(X22,u1_struct_0(X20))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~v8_lattices(X20)|~v9_lattices(X20)|~l3_lattices(X20)))&(k2_lattices(X20,X21,X22)!=X21|r1_lattices(X20,X21,X22)|~m1_subset_1(X22,u1_struct_0(X20))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~v8_lattices(X20)|~v9_lattices(X20)|~l3_lattices(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.48/0.65  cnf(c_0_38, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.48/0.65  cnf(c_0_39, negated_conjecture, (v9_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])]), c_0_26])).
% 0.48/0.65  cnf(c_0_40, negated_conjecture, (v8_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_24]), c_0_25])]), c_0_26])).
% 0.48/0.65  cnf(c_0_41, negated_conjecture, (v6_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_24]), c_0_25])]), c_0_26])).
% 0.48/0.65  cnf(c_0_42, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.48/0.65  cnf(c_0_43, negated_conjecture, (r3_lattices(esk7_0,k15_lattice3(esk7_0,X1),k15_lattice3(esk7_0,X2))|r2_hidden(esk6_3(esk7_0,X1,X2),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_24]), c_0_25])]), c_0_26])).
% 0.48/0.65  cnf(c_0_44, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.48/0.65  cnf(c_0_45, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.48/0.65  cnf(c_0_46, negated_conjecture, (l1_lattices(esk7_0)), inference(spm,[status(thm)],[c_0_35, c_0_25])).
% 0.48/0.65  fof(c_0_47, plain, ![X15]:(v2_struct_0(X15)|~l1_lattices(X15)|m1_subset_1(k5_lattices(X15),u1_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.48/0.65  fof(c_0_48, plain, ![X11, X12, X13]:(((k2_lattices(X11,X12,X13)=X12|~m1_subset_1(X13,u1_struct_0(X11))|X12!=k5_lattices(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~v13_lattices(X11)|(v2_struct_0(X11)|~l1_lattices(X11)))&(k2_lattices(X11,X13,X12)=X12|~m1_subset_1(X13,u1_struct_0(X11))|X12!=k5_lattices(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~v13_lattices(X11)|(v2_struct_0(X11)|~l1_lattices(X11))))&((m1_subset_1(esk1_2(X11,X12),u1_struct_0(X11))|X12=k5_lattices(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~v13_lattices(X11)|(v2_struct_0(X11)|~l1_lattices(X11)))&(k2_lattices(X11,X12,esk1_2(X11,X12))!=X12|k2_lattices(X11,esk1_2(X11,X12),X12)!=X12|X12=k5_lattices(X11)|~m1_subset_1(X12,u1_struct_0(X11))|~v13_lattices(X11)|(v2_struct_0(X11)|~l1_lattices(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.48/0.65  cnf(c_0_49, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.48/0.65  cnf(c_0_50, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.48/0.65  cnf(c_0_51, negated_conjecture, (r1_lattices(esk7_0,X1,X2)|~r3_lattices(esk7_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41]), c_0_25])]), c_0_26])).
% 0.48/0.65  cnf(c_0_52, negated_conjecture, (r3_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k15_lattice3(esk7_0,X1))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.48/0.65  cnf(c_0_53, negated_conjecture, (m1_subset_1(k15_lattice3(esk7_0,X1),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_25]), c_0_26])).
% 0.48/0.65  cnf(c_0_54, negated_conjecture, (k2_lattices(esk7_0,X1,X2)=k2_lattices(esk7_0,X2,X1)|~m1_subset_1(X2,u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_41])]), c_0_26])).
% 0.48/0.65  cnf(c_0_55, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.48/0.65  cnf(c_0_56, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.48/0.65  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk3_2(esk7_0,X1),u1_struct_0(esk7_0))|v13_lattices(esk7_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_46]), c_0_26])).
% 0.48/0.65  cnf(c_0_58, negated_conjecture, (k2_lattices(esk7_0,X1,X2)=X1|~r1_lattices(esk7_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_39]), c_0_40]), c_0_25])]), c_0_26])).
% 0.48/0.65  cnf(c_0_59, negated_conjecture, (r1_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k15_lattice3(esk7_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_53])])).
% 0.48/0.65  cnf(c_0_60, negated_conjecture, (k2_lattices(esk7_0,X1,k15_lattice3(esk7_0,X2))=k2_lattices(esk7_0,k15_lattice3(esk7_0,X2),X1)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_54, c_0_53])).
% 0.48/0.65  fof(c_0_61, plain, ![X35, X36]:((X36=k15_lattice3(X35,a_2_3_lattice3(X35,X36))|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)))&(X36=k16_lattice3(X35,a_2_4_lattice3(X35,X36))|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~v10_lattices(X35)|~v4_lattice3(X35)|~l3_lattices(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).
% 0.48/0.65  cnf(c_0_62, negated_conjecture, (m1_subset_1(k5_lattices(esk7_0),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_46]), c_0_26])).
% 0.48/0.65  cnf(c_0_63, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_56]), c_0_55])).
% 0.48/0.65  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),u1_struct_0(esk7_0))|v13_lattices(esk7_0)), inference(spm,[status(thm)],[c_0_57, c_0_53])).
% 0.48/0.65  cnf(c_0_65, negated_conjecture, (k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k15_lattice3(esk7_0,X1))=k15_lattice3(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_53]), c_0_53])])).
% 0.48/0.65  cnf(c_0_66, negated_conjecture, (k2_lattices(esk7_0,k15_lattice3(esk7_0,X1),k15_lattice3(esk7_0,X2))=k2_lattices(esk7_0,k15_lattice3(esk7_0,X2),k15_lattice3(esk7_0,X1))), inference(spm,[status(thm)],[c_0_60, c_0_53])).
% 0.48/0.65  cnf(c_0_67, plain, (X1=k15_lattice3(X2,a_2_3_lattice3(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.48/0.65  cnf(c_0_68, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k2_lattices(X1,X2,X3)!=X2|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.48/0.65  cnf(c_0_69, negated_conjecture, (k2_lattices(esk7_0,X1,k5_lattices(esk7_0))=k2_lattices(esk7_0,k5_lattices(esk7_0),X1)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_54, c_0_62])).
% 0.48/0.65  cnf(c_0_70, negated_conjecture, (k2_lattices(esk7_0,X1,k5_lattices(esk7_0))=k5_lattices(esk7_0)|m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,X2)),u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_46])]), c_0_26])).
% 0.48/0.65  cnf(c_0_71, plain, (m1_subset_1(esk2_1(X1),u1_struct_0(X1))|v2_struct_0(X1)|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.48/0.65  cnf(c_0_72, negated_conjecture, (k2_lattices(esk7_0,k15_lattice3(esk7_0,X1),k15_lattice3(esk7_0,k1_xboole_0))=k15_lattice3(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.48/0.65  cnf(c_0_73, negated_conjecture, (k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,X1))=X1|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_32]), c_0_24]), c_0_25])]), c_0_26])).
% 0.48/0.65  cnf(c_0_74, negated_conjecture, (r1_lattices(esk7_0,X1,X2)|k2_lattices(esk7_0,X1,X2)!=X1|~m1_subset_1(X2,u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_39]), c_0_40]), c_0_25])]), c_0_26])).
% 0.48/0.65  cnf(c_0_75, negated_conjecture, (k2_lattices(esk7_0,k15_lattice3(esk7_0,X1),k5_lattices(esk7_0))=k2_lattices(esk7_0,k5_lattices(esk7_0),k15_lattice3(esk7_0,X1))), inference(spm,[status(thm)],[c_0_69, c_0_53])).
% 0.48/0.65  cnf(c_0_76, negated_conjecture, (k2_lattices(esk7_0,k15_lattice3(esk7_0,X1),k5_lattices(esk7_0))=k5_lattices(esk7_0)|m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,X2)),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_70, c_0_53])).
% 0.48/0.65  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),u1_struct_0(esk7_0))|m1_subset_1(esk2_1(esk7_0),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_64]), c_0_46])]), c_0_26])).
% 0.48/0.65  cnf(c_0_78, negated_conjecture, (k15_lattice3(esk7_0,k1_xboole_0)=k15_lattice3(esk7_0,X1)|~r1_lattices(esk7_0,k15_lattice3(esk7_0,X1),k15_lattice3(esk7_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_72]), c_0_53]), c_0_53])])).
% 0.48/0.65  cnf(c_0_79, negated_conjecture, (k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,k5_lattices(esk7_0)))=k5_lattices(esk7_0)), inference(spm,[status(thm)],[c_0_73, c_0_62])).
% 0.48/0.65  cnf(c_0_80, negated_conjecture, (r1_lattices(esk7_0,k5_lattices(esk7_0),k15_lattice3(esk7_0,X1))|k2_lattices(esk7_0,k15_lattice3(esk7_0,X1),k5_lattices(esk7_0))!=k5_lattices(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_53]), c_0_62])])).
% 0.48/0.65  cnf(c_0_81, negated_conjecture, (k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1))))=esk3_2(esk7_0,k15_lattice3(esk7_0,X1))|k2_lattices(esk7_0,k15_lattice3(esk7_0,X2),k5_lattices(esk7_0))=k5_lattices(esk7_0)), inference(spm,[status(thm)],[c_0_73, c_0_76])).
% 0.48/0.65  cnf(c_0_82, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|k2_lattices(X1,esk3_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.48/0.65  cnf(c_0_83, negated_conjecture, (k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1))))=esk3_2(esk7_0,k15_lattice3(esk7_0,X1))|m1_subset_1(esk2_1(esk7_0),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_73, c_0_77])).
% 0.48/0.65  cnf(c_0_84, negated_conjecture, (k5_lattices(esk7_0)=k15_lattice3(esk7_0,k1_xboole_0)|~r1_lattices(esk7_0,k5_lattices(esk7_0),k15_lattice3(esk7_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.48/0.65  cnf(c_0_85, negated_conjecture, (k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1))))=esk3_2(esk7_0,k15_lattice3(esk7_0,X1))|r1_lattices(esk7_0,k5_lattices(esk7_0),k15_lattice3(esk7_0,X2))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.48/0.65  cnf(c_0_86, negated_conjecture, (v13_lattices(esk7_0)|k2_lattices(esk7_0,X1,esk3_2(esk7_0,X1))!=X1|k2_lattices(esk7_0,esk3_2(esk7_0,X1),X1)!=X1|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_46]), c_0_26])).
% 0.48/0.65  cnf(c_0_87, negated_conjecture, (k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1))))=esk3_2(esk7_0,k15_lattice3(esk7_0,X1))|k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk2_1(esk7_0)))=esk2_1(esk7_0)), inference(spm,[status(thm)],[c_0_73, c_0_83])).
% 0.48/0.65  cnf(c_0_88, negated_conjecture, (k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1))))=esk3_2(esk7_0,k15_lattice3(esk7_0,X1))|k5_lattices(esk7_0)=k15_lattice3(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.48/0.65  cnf(c_0_89, negated_conjecture, (v13_lattices(esk7_0)|k2_lattices(esk7_0,k15_lattice3(esk7_0,X1),esk3_2(esk7_0,k15_lattice3(esk7_0,X1)))!=k15_lattice3(esk7_0,X1)|k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),k15_lattice3(esk7_0,X1))!=k15_lattice3(esk7_0,X1)), inference(spm,[status(thm)],[c_0_86, c_0_53])).
% 0.48/0.65  cnf(c_0_90, negated_conjecture, (k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),esk3_2(esk7_0,k15_lattice3(esk7_0,X1)))=k15_lattice3(esk7_0,k1_xboole_0)|k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk2_1(esk7_0)))=esk2_1(esk7_0)), inference(spm,[status(thm)],[c_0_65, c_0_87])).
% 0.48/0.65  cnf(c_0_91, negated_conjecture, (k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),esk3_2(esk7_0,k15_lattice3(esk7_0,X1)))=k15_lattice3(esk7_0,k1_xboole_0)|k5_lattices(esk7_0)=k15_lattice3(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_88])).
% 0.48/0.65  cnf(c_0_92, negated_conjecture, (k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk2_1(esk7_0)))=esk2_1(esk7_0)|v13_lattices(esk7_0)|k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0)),k15_lattice3(esk7_0,k1_xboole_0))!=k15_lattice3(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.48/0.65  cnf(c_0_93, negated_conjecture, (k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),k15_lattice3(esk7_0,k1_xboole_0))=k15_lattice3(esk7_0,k1_xboole_0)|k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk2_1(esk7_0)))=esk2_1(esk7_0)), inference(spm,[status(thm)],[c_0_72, c_0_87])).
% 0.48/0.65  cnf(c_0_94, negated_conjecture, (k5_lattices(esk7_0)=k15_lattice3(esk7_0,k1_xboole_0)|v13_lattices(esk7_0)|k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0)),k15_lattice3(esk7_0,k1_xboole_0))!=k15_lattice3(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_89, c_0_91])).
% 0.48/0.65  cnf(c_0_95, negated_conjecture, (k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),k15_lattice3(esk7_0,k1_xboole_0))=k15_lattice3(esk7_0,k1_xboole_0)|k5_lattices(esk7_0)=k15_lattice3(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_72, c_0_88])).
% 0.48/0.65  cnf(c_0_96, plain, (k2_lattices(X1,X2,esk2_1(X1))=esk2_1(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.48/0.65  cnf(c_0_97, negated_conjecture, (k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk2_1(esk7_0)))=esk2_1(esk7_0)|v13_lattices(esk7_0)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.48/0.65  cnf(c_0_98, negated_conjecture, (k5_lattices(esk7_0)=k15_lattice3(esk7_0,k1_xboole_0)|v13_lattices(esk7_0)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.48/0.65  cnf(c_0_99, negated_conjecture, (k2_lattices(esk7_0,X1,esk2_1(esk7_0))=esk2_1(esk7_0)|m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,X2)),u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_64]), c_0_46])]), c_0_26])).
% 0.48/0.65  cnf(c_0_100, negated_conjecture, (k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk2_1(esk7_0)))=esk2_1(esk7_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_97]), c_0_46])]), c_0_26]), c_0_73])).
% 0.48/0.65  cnf(c_0_101, negated_conjecture, (k2_lattices(esk7_0,X1,esk2_1(esk7_0))=esk2_1(esk7_0)|k5_lattices(esk7_0)=k15_lattice3(esk7_0,k1_xboole_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_98]), c_0_46])]), c_0_26])).
% 0.48/0.65  cnf(c_0_102, negated_conjecture, (r3_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k5_lattices(esk7_0))), inference(spm,[status(thm)],[c_0_52, c_0_79])).
% 0.48/0.65  cnf(c_0_103, negated_conjecture, (k2_lattices(esk7_0,k5_lattices(esk7_0),esk2_1(esk7_0))=esk2_1(esk7_0)|m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_99, c_0_62])).
% 0.48/0.65  cnf(c_0_104, negated_conjecture, (k2_lattices(esk7_0,X1,k5_lattices(esk7_0))=k5_lattices(esk7_0)|k5_lattices(esk7_0)=k15_lattice3(esk7_0,k1_xboole_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_98]), c_0_46])]), c_0_26])).
% 0.48/0.65  cnf(c_0_105, negated_conjecture, (m1_subset_1(esk2_1(esk7_0),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_100]), c_0_25])]), c_0_26])).
% 0.48/0.65  cnf(c_0_106, negated_conjecture, (k2_lattices(esk7_0,esk2_1(esk7_0),k5_lattices(esk7_0))=k2_lattices(esk7_0,k5_lattices(esk7_0),esk2_1(esk7_0))), inference(spm,[status(thm)],[c_0_75, c_0_100])).
% 0.48/0.65  cnf(c_0_107, negated_conjecture, (k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),esk2_1(esk7_0))=k15_lattice3(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_100])).
% 0.48/0.65  cnf(c_0_108, negated_conjecture, (k2_lattices(esk7_0,k15_lattice3(esk7_0,X1),esk2_1(esk7_0))=esk2_1(esk7_0)|k5_lattices(esk7_0)=k15_lattice3(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_101, c_0_53])).
% 0.48/0.65  cnf(c_0_109, negated_conjecture, (r1_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k5_lattices(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_102]), c_0_62]), c_0_53])])).
% 0.48/0.65  cnf(c_0_110, negated_conjecture, (k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1))))=esk3_2(esk7_0,k15_lattice3(esk7_0,X1))|k2_lattices(esk7_0,k5_lattices(esk7_0),esk2_1(esk7_0))=esk2_1(esk7_0)), inference(spm,[status(thm)],[c_0_73, c_0_103])).
% 0.48/0.65  cnf(c_0_111, negated_conjecture, (v2_struct_0(esk7_0)|~v10_lattices(esk7_0)|~v13_lattices(esk7_0)|~l3_lattices(esk7_0)|k5_lattices(esk7_0)!=k15_lattice3(esk7_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.48/0.65  cnf(c_0_112, negated_conjecture, (k2_lattices(esk7_0,k5_lattices(esk7_0),esk2_1(esk7_0))=k5_lattices(esk7_0)|k5_lattices(esk7_0)=k15_lattice3(esk7_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_106])).
% 0.48/0.65  cnf(c_0_113, negated_conjecture, (k5_lattices(esk7_0)=k15_lattice3(esk7_0,k1_xboole_0)|esk2_1(esk7_0)=k15_lattice3(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 0.48/0.65  cnf(c_0_114, negated_conjecture, (k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),k5_lattices(esk7_0))=k15_lattice3(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_109]), c_0_62]), c_0_53])])).
% 0.48/0.65  cnf(c_0_115, negated_conjecture, (k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),esk3_2(esk7_0,k15_lattice3(esk7_0,X1)))=k15_lattice3(esk7_0,k1_xboole_0)|k2_lattices(esk7_0,k5_lattices(esk7_0),esk2_1(esk7_0))=esk2_1(esk7_0)), inference(spm,[status(thm)],[c_0_65, c_0_110])).
% 0.48/0.65  cnf(c_0_116, negated_conjecture, (k5_lattices(esk7_0)!=k15_lattice3(esk7_0,k1_xboole_0)|~v13_lattices(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_25]), c_0_24])]), c_0_26])).
% 0.48/0.65  cnf(c_0_117, negated_conjecture, (k5_lattices(esk7_0)=k15_lattice3(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_75]), c_0_114])])).
% 0.48/0.65  cnf(c_0_118, negated_conjecture, (k2_lattices(esk7_0,k5_lattices(esk7_0),esk2_1(esk7_0))=esk2_1(esk7_0)|v13_lattices(esk7_0)|k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0)),k15_lattice3(esk7_0,k1_xboole_0))!=k15_lattice3(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_89, c_0_115])).
% 0.48/0.65  cnf(c_0_119, negated_conjecture, (k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),k15_lattice3(esk7_0,k1_xboole_0))=k15_lattice3(esk7_0,k1_xboole_0)|k2_lattices(esk7_0,k5_lattices(esk7_0),esk2_1(esk7_0))=esk2_1(esk7_0)), inference(spm,[status(thm)],[c_0_72, c_0_110])).
% 0.48/0.65  cnf(c_0_120, negated_conjecture, (~v13_lattices(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_117])])).
% 0.48/0.65  cnf(c_0_121, negated_conjecture, (k2_lattices(esk7_0,k5_lattices(esk7_0),esk2_1(esk7_0))=esk2_1(esk7_0)|v13_lattices(esk7_0)), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 0.48/0.65  cnf(c_0_122, negated_conjecture, (m1_subset_1(esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[c_0_64, c_0_120])).
% 0.48/0.65  cnf(c_0_123, negated_conjecture, (v13_lattices(esk7_0)|k2_lattices(esk7_0,esk2_1(esk7_0),esk3_2(esk7_0,esk2_1(esk7_0)))!=esk2_1(esk7_0)|k2_lattices(esk7_0,esk3_2(esk7_0,esk2_1(esk7_0)),esk2_1(esk7_0))!=esk2_1(esk7_0)), inference(spm,[status(thm)],[c_0_89, c_0_100])).
% 0.48/0.65  cnf(c_0_124, negated_conjecture, (esk2_1(esk7_0)=k15_lattice3(esk7_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_117]), c_0_107]), c_0_120])).
% 0.48/0.65  cnf(c_0_125, negated_conjecture, (k15_lattice3(esk7_0,a_2_3_lattice3(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1))))=esk3_2(esk7_0,k15_lattice3(esk7_0,X1))), inference(spm,[status(thm)],[c_0_73, c_0_122])).
% 0.48/0.65  cnf(c_0_126, negated_conjecture, (k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),esk3_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0)))!=k15_lattice3(esk7_0,k1_xboole_0)|k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0)),k15_lattice3(esk7_0,k1_xboole_0))!=k15_lattice3(esk7_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_124]), c_0_124]), c_0_124]), c_0_124]), c_0_124]), c_0_124]), c_0_120])).
% 0.48/0.65  cnf(c_0_127, negated_conjecture, (k2_lattices(esk7_0,k15_lattice3(esk7_0,k1_xboole_0),esk3_2(esk7_0,k15_lattice3(esk7_0,X1)))=k15_lattice3(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_125])).
% 0.48/0.65  cnf(c_0_128, negated_conjecture, (k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,k1_xboole_0)),k15_lattice3(esk7_0,k1_xboole_0))!=k15_lattice3(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_127])])).
% 0.48/0.65  cnf(c_0_129, negated_conjecture, (k2_lattices(esk7_0,esk3_2(esk7_0,k15_lattice3(esk7_0,X1)),k15_lattice3(esk7_0,k1_xboole_0))=k15_lattice3(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_72, c_0_125])).
% 0.48/0.65  cnf(c_0_130, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_129])]), ['proof']).
% 0.48/0.65  # SZS output end CNFRefutation
% 0.48/0.65  # Proof object total steps             : 131
% 0.48/0.65  # Proof object clause steps            : 102
% 0.48/0.65  # Proof object formula steps           : 29
% 0.48/0.65  # Proof object conjectures             : 83
% 0.48/0.65  # Proof object clause conjectures      : 80
% 0.48/0.65  # Proof object formula conjectures     : 3
% 0.48/0.65  # Proof object initial clauses used    : 24
% 0.48/0.65  # Proof object initial formulas used   : 14
% 0.48/0.65  # Proof object generating inferences   : 69
% 0.48/0.65  # Proof object simplifying inferences  : 105
% 0.48/0.65  # Training examples: 0 positive, 0 negative
% 0.48/0.65  # Parsed axioms                        : 14
% 0.48/0.65  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.65  # Initial clauses                      : 42
% 0.48/0.65  # Removed in clause preprocessing      : 1
% 0.48/0.65  # Initial clauses in saturation        : 41
% 0.48/0.65  # Processed clauses                    : 2729
% 0.48/0.65  # ...of these trivial                  : 36
% 0.48/0.65  # ...subsumed                          : 1559
% 0.48/0.65  # ...remaining for further processing  : 1134
% 0.48/0.65  # Other redundant clauses eliminated   : 6
% 0.48/0.65  # Clauses deleted for lack of memory   : 0
% 0.48/0.65  # Backward-subsumed                    : 148
% 0.48/0.65  # Backward-rewritten                   : 802
% 0.48/0.65  # Generated clauses                    : 18318
% 0.48/0.65  # ...of the previous two non-trivial   : 18160
% 0.48/0.65  # Contextual simplify-reflections      : 21
% 0.48/0.65  # Paramodulations                      : 18278
% 0.48/0.65  # Factorizations                       : 15
% 0.48/0.65  # Equation resolutions                 : 7
% 0.48/0.65  # Propositional unsat checks           : 0
% 0.48/0.65  #    Propositional check models        : 0
% 0.48/0.65  #    Propositional check unsatisfiable : 0
% 0.48/0.65  #    Propositional clauses             : 0
% 0.48/0.65  #    Propositional clauses after purity: 0
% 0.48/0.65  #    Propositional unsat core size     : 0
% 0.48/0.65  #    Propositional preprocessing time  : 0.000
% 0.48/0.65  #    Propositional encoding time       : 0.000
% 0.48/0.65  #    Propositional solver time         : 0.000
% 0.48/0.65  #    Success case prop preproc time    : 0.000
% 0.48/0.65  #    Success case prop encoding time   : 0.000
% 0.48/0.65  #    Success case prop solver time     : 0.000
% 0.48/0.65  # Current number of processed clauses  : 121
% 0.48/0.65  #    Positive orientable unit clauses  : 30
% 0.48/0.65  #    Positive unorientable unit clauses: 1
% 0.48/0.65  #    Negative unit clauses             : 4
% 0.48/0.65  #    Non-unit-clauses                  : 86
% 0.48/0.65  # Current number of unprocessed clauses: 15063
% 0.48/0.65  # ...number of literals in the above   : 57094
% 0.48/0.65  # Current number of archived formulas  : 0
% 0.48/0.65  # Current number of archived clauses   : 1009
% 0.48/0.65  # Clause-clause subsumption calls (NU) : 68658
% 0.48/0.65  # Rec. Clause-clause subsumption calls : 33876
% 0.48/0.65  # Non-unit clause-clause subsumptions  : 1665
% 0.48/0.65  # Unit Clause-clause subsumption calls : 1377
% 0.48/0.65  # Rewrite failures with RHS unbound    : 0
% 0.48/0.65  # BW rewrite match attempts            : 120
% 0.48/0.65  # BW rewrite match successes           : 21
% 0.48/0.65  # Condensation attempts                : 0
% 0.48/0.65  # Condensation successes               : 0
% 0.48/0.65  # Termbank termtop insertions          : 532829
% 0.48/0.65  
% 0.48/0.65  # -------------------------------------------------
% 0.48/0.65  # User time                : 0.294 s
% 0.48/0.65  # System time              : 0.010 s
% 0.48/0.65  # Total time               : 0.304 s
% 0.48/0.65  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
