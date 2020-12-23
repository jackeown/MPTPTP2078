%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:09 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 (1368 expanded)
%              Number of clauses        :   59 ( 484 expanded)
%              Number of leaves         :   15 ( 335 expanded)
%              Depth                    :   14
%              Number of atoms          :  458 (8897 expanded)
%              Number of equality atoms :   66 ( 858 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   28 (   3 average)
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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(t43_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
            & k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattice3)).

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
    ! [X13,X14] :
      ( ( k2_zfmisc_1(X13,X14) != k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_17,plain,(
    ! [X52,X53,X54,X56] :
      ( ( m1_subset_1(esk9_3(X52,X53,X54),u1_struct_0(X52))
        | r3_lattices(X52,k15_lattice3(X52,X53),k15_lattice3(X52,X54))
        | v2_struct_0(X52)
        | ~ v10_lattices(X52)
        | ~ v4_lattice3(X52)
        | ~ l3_lattices(X52) )
      & ( r2_hidden(esk9_3(X52,X53,X54),X53)
        | r3_lattices(X52,k15_lattice3(X52,X53),k15_lattice3(X52,X54))
        | v2_struct_0(X52)
        | ~ v10_lattices(X52)
        | ~ v4_lattice3(X52)
        | ~ l3_lattices(X52) )
      & ( ~ m1_subset_1(X56,u1_struct_0(X52))
        | ~ r3_lattices(X52,esk9_3(X52,X53,X54),X56)
        | ~ r2_hidden(X56,X54)
        | r3_lattices(X52,k15_lattice3(X52,X53),k15_lattice3(X52,X54))
        | v2_struct_0(X52)
        | ~ v10_lattices(X52)
        | ~ v4_lattice3(X52)
        | ~ l3_lattices(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk10_0)
    & v10_lattices(esk10_0)
    & v4_lattice3(esk10_0)
    & l3_lattices(esk10_0)
    & ( v2_struct_0(esk10_0)
      | ~ v10_lattices(esk10_0)
      | ~ v13_lattices(esk10_0)
      | ~ l3_lattices(esk10_0)
      | k5_lattices(esk10_0) != k15_lattice3(esk10_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_19,plain,(
    ! [X15,X16] : ~ r2_hidden(X15,k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_20,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X22] :
      ( v2_struct_0(X22)
      | ~ l1_lattices(X22)
      | m1_subset_1(k5_lattices(X22),u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_22,plain,(
    ! [X23] :
      ( ( l1_lattices(X23)
        | ~ l3_lattices(X23) )
      & ( l2_lattices(X23)
        | ~ l3_lattices(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_23,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(esk9_3(X1,X2,X3),X2)
    | r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v4_lattice3(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v10_lattices(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( l3_lattices(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_20])).

fof(c_0_31,plain,(
    ! [X40,X41] :
      ( v2_struct_0(X40)
      | ~ l3_lattices(X40)
      | m1_subset_1(k15_lattice3(X40,X41),u1_struct_0(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

fof(c_0_32,plain,(
    ! [X17] :
      ( ( ~ v2_struct_0(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v4_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v5_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v6_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v7_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v8_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( v9_lattices(X17)
        | v2_struct_0(X17)
        | ~ v10_lattices(X17)
        | ~ l3_lattices(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( r3_lattices(esk10_0,k15_lattice3(esk10_0,X1),k15_lattice3(esk10_0,X2))
    | r2_hidden(esk9_3(esk10_0,X1,X2),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_39,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r1_lattices(X27,X28,X29)
        | k2_lattices(X27,X28,X29) = X28
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v8_lattices(X27)
        | ~ v9_lattices(X27)
        | ~ l3_lattices(X27) )
      & ( k2_lattices(X27,X28,X29) != X28
        | r1_lattices(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v8_lattices(X27)
        | ~ v9_lattices(X27)
        | ~ l3_lattices(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_43,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r3_lattices(X24,X25,X26)
        | r1_lattices(X24,X25,X26)
        | v2_struct_0(X24)
        | ~ v6_lattices(X24)
        | ~ v8_lattices(X24)
        | ~ v9_lattices(X24)
        | ~ l3_lattices(X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24)) )
      & ( ~ r1_lattices(X24,X25,X26)
        | r3_lattices(X24,X25,X26)
        | v2_struct_0(X24)
        | ~ v6_lattices(X24)
        | ~ v8_lattices(X24)
        | ~ v9_lattices(X24)
        | ~ l3_lattices(X24)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X24)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_44,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_45,plain,(
    ! [X30,X32,X33] :
      ( ( m1_subset_1(esk3_1(X30),u1_struct_0(X30))
        | ~ v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( k2_lattices(X30,esk3_1(X30),X32) = esk3_1(X30)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( k2_lattices(X30,X32,esk3_1(X30)) = esk3_1(X30)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( m1_subset_1(esk4_2(X30,X33),u1_struct_0(X30))
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( k2_lattices(X30,X33,esk4_2(X30,X33)) != X33
        | k2_lattices(X30,esk4_2(X30,X33),X33) != X33
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | v13_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).

cnf(c_0_46,plain,
    ( m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( r3_lattices(esk10_0,k15_lattice3(esk10_0,X1),k15_lattice3(esk10_0,X2))
    | r2_hidden(esk9_3(esk10_0,X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_49,plain,(
    ! [X50,X51] :
      ( ( k15_lattice3(X50,k6_domain_1(u1_struct_0(X50),X51)) = X51
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50) )
      & ( k16_lattice3(X50,k6_domain_1(u1_struct_0(X50),X51)) = X51
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_lattice3])])])])])).

cnf(c_0_50,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk10_0,X1),u1_struct_0(esk10_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_27]),c_0_28])).

cnf(c_0_52,negated_conjecture,
    ( v9_lattices(esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_53,negated_conjecture,
    ( v8_lattices(esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_54,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( v6_lattices(esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_56,plain,
    ( m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_57,plain,(
    ! [X18,X19,X20] :
      ( ( k2_lattices(X18,X19,X20) = X19
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | X19 != k5_lattices(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) )
      & ( k2_lattices(X18,X20,X19) = X19
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | X19 != k5_lattices(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) )
      & ( m1_subset_1(esk2_2(X18,X19),u1_struct_0(X18))
        | X19 = k5_lattices(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) )
      & ( k2_lattices(X18,X19,esk2_2(X18,X19)) != X19
        | k2_lattices(X18,esk2_2(X18,X19),X19) != X19
        | X19 = k5_lattices(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ v13_lattices(X18)
        | v2_struct_0(X18)
        | ~ l1_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk10_0),u1_struct_0(esk10_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_27]),c_0_28])).

cnf(c_0_59,negated_conjecture,
    ( r3_lattices(esk10_0,k15_lattice3(esk10_0,k1_xboole_0),k15_lattice3(esk10_0,X1))
    | r2_hidden(esk9_3(esk10_0,k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_60,plain,
    ( k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( k2_lattices(esk10_0,X1,k15_lattice3(esk10_0,X2)) = X1
    | ~ r1_lattices(esk10_0,X1,k15_lattice3(esk10_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53]),c_0_27])]),c_0_28])).

cnf(c_0_62,negated_conjecture,
    ( r1_lattices(esk10_0,X1,k15_lattice3(esk10_0,X2))
    | ~ r3_lattices(esk10_0,X1,k15_lattice3(esk10_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_51]),c_0_52]),c_0_53]),c_0_55]),c_0_27])]),c_0_28])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk4_2(esk10_0,k15_lattice3(esk10_0,X1)),u1_struct_0(esk10_0))
    | v13_lattices(esk10_0)
    | ~ l1_lattices(esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_51]),c_0_28])).

cnf(c_0_64,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( k2_lattices(esk10_0,X1,k5_lattices(esk10_0)) = X1
    | ~ r1_lattices(esk10_0,X1,k5_lattices(esk10_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_58]),c_0_52]),c_0_53]),c_0_27])]),c_0_28])).

cnf(c_0_66,negated_conjecture,
    ( r1_lattices(esk10_0,X1,k5_lattices(esk10_0))
    | ~ r3_lattices(esk10_0,X1,k5_lattices(esk10_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_58]),c_0_52]),c_0_53]),c_0_55]),c_0_27])]),c_0_28])).

cnf(c_0_67,negated_conjecture,
    ( r3_lattices(esk10_0,k15_lattice3(esk10_0,k1_xboole_0),k15_lattice3(esk10_0,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( k15_lattice3(esk10_0,k6_domain_1(u1_struct_0(esk10_0),k5_lattices(esk10_0))) = k5_lattices(esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_58]),c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_69,negated_conjecture,
    ( k2_lattices(esk10_0,X1,k15_lattice3(esk10_0,X2)) = X1
    | ~ r3_lattices(esk10_0,X1,k15_lattice3(esk10_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk4_2(esk10_0,k15_lattice3(esk10_0,X1)),u1_struct_0(esk10_0))
    | v13_lattices(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_34]),c_0_27])])).

cnf(c_0_71,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_64]),c_0_33])).

cnf(c_0_72,negated_conjecture,
    ( k2_lattices(esk10_0,X1,k5_lattices(esk10_0)) = X1
    | ~ r3_lattices(esk10_0,X1,k5_lattices(esk10_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( r3_lattices(esk10_0,k15_lattice3(esk10_0,k1_xboole_0),k5_lattices(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( v2_struct_0(esk10_0)
    | ~ v10_lattices(esk10_0)
    | ~ v13_lattices(esk10_0)
    | ~ l3_lattices(esk10_0)
    | k5_lattices(esk10_0) != k15_lattice3(esk10_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_75,negated_conjecture,
    ( k2_lattices(esk10_0,k15_lattice3(esk10_0,k1_xboole_0),k15_lattice3(esk10_0,X1)) = k15_lattice3(esk10_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_67]),c_0_51])])).

cnf(c_0_76,negated_conjecture,
    ( k15_lattice3(esk10_0,k6_domain_1(u1_struct_0(esk10_0),esk4_2(esk10_0,k15_lattice3(esk10_0,X1)))) = esk4_2(esk10_0,k15_lattice3(esk10_0,X1))
    | v13_lattices(esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_70]),c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_77,negated_conjecture,
    ( k2_lattices(esk10_0,k15_lattice3(esk10_0,X1),k5_lattices(esk10_0)) = k5_lattices(esk10_0)
    | ~ v13_lattices(esk10_0)
    | ~ l1_lattices(esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_51]),c_0_28])).

cnf(c_0_78,negated_conjecture,
    ( k2_lattices(esk10_0,k15_lattice3(esk10_0,k1_xboole_0),k5_lattices(esk10_0)) = k15_lattice3(esk10_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_51])])).

cnf(c_0_79,negated_conjecture,
    ( k5_lattices(esk10_0) != k15_lattice3(esk10_0,k1_xboole_0)
    | ~ v13_lattices(esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_27]),c_0_26])]),c_0_28])).

fof(c_0_80,plain,(
    ! [X35,X36,X37] :
      ( ( ~ v6_lattices(X35)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | k2_lattices(X35,X36,X37) = k2_lattices(X35,X37,X36)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( m1_subset_1(esk5_1(X35),u1_struct_0(X35))
        | v6_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( m1_subset_1(esk6_1(X35),u1_struct_0(X35))
        | v6_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) )
      & ( k2_lattices(X35,esk5_1(X35),esk6_1(X35)) != k2_lattices(X35,esk6_1(X35),esk5_1(X35))
        | v6_lattices(X35)
        | v2_struct_0(X35)
        | ~ l1_lattices(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

cnf(c_0_81,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk4_2(X1,X2)) != X2
    | k2_lattices(X1,esk4_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_82,negated_conjecture,
    ( k2_lattices(esk10_0,k15_lattice3(esk10_0,k1_xboole_0),esk4_2(esk10_0,k15_lattice3(esk10_0,X1))) = k15_lattice3(esk10_0,k1_xboole_0)
    | v13_lattices(esk10_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( ~ v13_lattices(esk10_0)
    | ~ l1_lattices(esk10_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])).

cnf(c_0_84,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( k2_lattices(esk10_0,esk4_2(esk10_0,k15_lattice3(esk10_0,k1_xboole_0)),k15_lattice3(esk10_0,k1_xboole_0)) != k15_lattice3(esk10_0,k1_xboole_0)
    | ~ l1_lattices(esk10_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_51])]),c_0_28]),c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( k2_lattices(esk10_0,X1,esk4_2(esk10_0,k15_lattice3(esk10_0,X2))) = k2_lattices(esk10_0,esk4_2(esk10_0,k15_lattice3(esk10_0,X2)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk10_0))
    | ~ l1_lattices(esk10_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_70]),c_0_55])]),c_0_28]),c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( k2_lattices(esk10_0,k15_lattice3(esk10_0,k1_xboole_0),esk4_2(esk10_0,k15_lattice3(esk10_0,k1_xboole_0))) != k15_lattice3(esk10_0,k1_xboole_0)
    | ~ l1_lattices(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_51])])).

cnf(c_0_88,negated_conjecture,
    ( ~ l1_lattices(esk10_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_82]),c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_34]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n018.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 10:12:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.44  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.030 s
% 0.19/0.44  # Presaturation interreduction done
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_lattice3)).
% 0.19/0.44  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.44  fof(t48_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_lattice3)).
% 0.19/0.44  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.19/0.44  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.19/0.44  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.19/0.44  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.44  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.19/0.44  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.19/0.44  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 0.19/0.44  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.19/0.44  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_lattices)).
% 0.19/0.44  fof(t43_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2&k16_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_lattice3)).
% 0.19/0.44  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 0.19/0.44  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_lattices)).
% 0.19/0.44  fof(c_0_15, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 0.19/0.44  fof(c_0_16, plain, ![X13, X14]:((k2_zfmisc_1(X13,X14)!=k1_xboole_0|(X13=k1_xboole_0|X14=k1_xboole_0))&((X13!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0)&(X14!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.44  fof(c_0_17, plain, ![X52, X53, X54, X56]:((m1_subset_1(esk9_3(X52,X53,X54),u1_struct_0(X52))|r3_lattices(X52,k15_lattice3(X52,X53),k15_lattice3(X52,X54))|(v2_struct_0(X52)|~v10_lattices(X52)|~v4_lattice3(X52)|~l3_lattices(X52)))&((r2_hidden(esk9_3(X52,X53,X54),X53)|r3_lattices(X52,k15_lattice3(X52,X53),k15_lattice3(X52,X54))|(v2_struct_0(X52)|~v10_lattices(X52)|~v4_lattice3(X52)|~l3_lattices(X52)))&(~m1_subset_1(X56,u1_struct_0(X52))|(~r3_lattices(X52,esk9_3(X52,X53,X54),X56)|~r2_hidden(X56,X54))|r3_lattices(X52,k15_lattice3(X52,X53),k15_lattice3(X52,X54))|(v2_struct_0(X52)|~v10_lattices(X52)|~v4_lattice3(X52)|~l3_lattices(X52))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).
% 0.19/0.44  fof(c_0_18, negated_conjecture, ((((~v2_struct_0(esk10_0)&v10_lattices(esk10_0))&v4_lattice3(esk10_0))&l3_lattices(esk10_0))&(v2_struct_0(esk10_0)|~v10_lattices(esk10_0)|~v13_lattices(esk10_0)|~l3_lattices(esk10_0)|k5_lattices(esk10_0)!=k15_lattice3(esk10_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.19/0.44  fof(c_0_19, plain, ![X15, X16]:~r2_hidden(X15,k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.19/0.44  cnf(c_0_20, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.44  fof(c_0_21, plain, ![X22]:(v2_struct_0(X22)|~l1_lattices(X22)|m1_subset_1(k5_lattices(X22),u1_struct_0(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.19/0.44  fof(c_0_22, plain, ![X23]:((l1_lattices(X23)|~l3_lattices(X23))&(l2_lattices(X23)|~l3_lattices(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.19/0.44  fof(c_0_23, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.44  cnf(c_0_24, plain, (r2_hidden(esk9_3(X1,X2,X3),X2)|r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  cnf(c_0_25, negated_conjecture, (v4_lattice3(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_26, negated_conjecture, (v10_lattices(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_27, negated_conjecture, (l3_lattices(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_29, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_30, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_20])).
% 0.19/0.44  fof(c_0_31, plain, ![X40, X41]:(v2_struct_0(X40)|~l3_lattices(X40)|m1_subset_1(k15_lattice3(X40,X41),u1_struct_0(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.19/0.44  fof(c_0_32, plain, ![X17]:(((((((~v2_struct_0(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17))&(v4_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17)))&(v5_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17)))&(v6_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17)))&(v7_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17)))&(v8_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17)))&(v9_lattices(X17)|(v2_struct_0(X17)|~v10_lattices(X17))|~l3_lattices(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.19/0.44  cnf(c_0_33, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.44  cnf(c_0_34, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.44  cnf(c_0_35, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.44  cnf(c_0_36, negated_conjecture, (r3_lattices(esk10_0,k15_lattice3(esk10_0,X1),k15_lattice3(esk10_0,X2))|r2_hidden(esk9_3(esk10_0,X1,X2),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.44  cnf(c_0_37, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.44  cnf(c_0_38, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.44  fof(c_0_39, plain, ![X27, X28, X29]:((~r1_lattices(X27,X28,X29)|k2_lattices(X27,X28,X29)=X28|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~v8_lattices(X27)|~v9_lattices(X27)|~l3_lattices(X27)))&(k2_lattices(X27,X28,X29)!=X28|r1_lattices(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~v8_lattices(X27)|~v9_lattices(X27)|~l3_lattices(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.19/0.44  cnf(c_0_40, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.44  cnf(c_0_41, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.44  cnf(c_0_42, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.44  fof(c_0_43, plain, ![X24, X25, X26]:((~r3_lattices(X24,X25,X26)|r1_lattices(X24,X25,X26)|(v2_struct_0(X24)|~v6_lattices(X24)|~v8_lattices(X24)|~v9_lattices(X24)|~l3_lattices(X24)|~m1_subset_1(X25,u1_struct_0(X24))|~m1_subset_1(X26,u1_struct_0(X24))))&(~r1_lattices(X24,X25,X26)|r3_lattices(X24,X25,X26)|(v2_struct_0(X24)|~v6_lattices(X24)|~v8_lattices(X24)|~v9_lattices(X24)|~l3_lattices(X24)|~m1_subset_1(X25,u1_struct_0(X24))|~m1_subset_1(X26,u1_struct_0(X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.19/0.44  cnf(c_0_44, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.44  fof(c_0_45, plain, ![X30, X32, X33]:(((m1_subset_1(esk3_1(X30),u1_struct_0(X30))|~v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))&((k2_lattices(X30,esk3_1(X30),X32)=esk3_1(X30)|~m1_subset_1(X32,u1_struct_0(X30))|~v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))&(k2_lattices(X30,X32,esk3_1(X30))=esk3_1(X30)|~m1_subset_1(X32,u1_struct_0(X30))|~v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))))&((m1_subset_1(esk4_2(X30,X33),u1_struct_0(X30))|~m1_subset_1(X33,u1_struct_0(X30))|v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))&(k2_lattices(X30,X33,esk4_2(X30,X33))!=X33|k2_lattices(X30,esk4_2(X30,X33),X33)!=X33|~m1_subset_1(X33,u1_struct_0(X30))|v13_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 0.19/0.44  cnf(c_0_46, plain, (m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.44  cnf(c_0_47, negated_conjecture, (r3_lattices(esk10_0,k15_lattice3(esk10_0,X1),k15_lattice3(esk10_0,X2))|r2_hidden(esk9_3(esk10_0,X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.44  cnf(c_0_48, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.44  fof(c_0_49, plain, ![X50, X51]:((k15_lattice3(X50,k6_domain_1(u1_struct_0(X50),X51))=X51|~m1_subset_1(X51,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50)))&(k16_lattice3(X50,k6_domain_1(u1_struct_0(X50),X51))=X51|~m1_subset_1(X51,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_lattice3])])])])])).
% 0.19/0.44  cnf(c_0_50, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.44  cnf(c_0_51, negated_conjecture, (m1_subset_1(k15_lattice3(esk10_0,X1),u1_struct_0(esk10_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_27]), c_0_28])).
% 0.19/0.44  cnf(c_0_52, negated_conjecture, (v9_lattices(esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.44  cnf(c_0_53, negated_conjecture, (v8_lattices(esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.44  cnf(c_0_54, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~r3_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.44  cnf(c_0_55, negated_conjecture, (v6_lattices(esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.44  cnf(c_0_56, plain, (m1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.44  fof(c_0_57, plain, ![X18, X19, X20]:(((k2_lattices(X18,X19,X20)=X19|~m1_subset_1(X20,u1_struct_0(X18))|X19!=k5_lattices(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18)))&(k2_lattices(X18,X20,X19)=X19|~m1_subset_1(X20,u1_struct_0(X18))|X19!=k5_lattices(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18))))&((m1_subset_1(esk2_2(X18,X19),u1_struct_0(X18))|X19=k5_lattices(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18)))&(k2_lattices(X18,X19,esk2_2(X18,X19))!=X19|k2_lattices(X18,esk2_2(X18,X19),X19)!=X19|X19=k5_lattices(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~v13_lattices(X18)|(v2_struct_0(X18)|~l1_lattices(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.19/0.44  cnf(c_0_58, negated_conjecture, (m1_subset_1(k5_lattices(esk10_0),u1_struct_0(esk10_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_27]), c_0_28])).
% 0.19/0.44  cnf(c_0_59, negated_conjecture, (r3_lattices(esk10_0,k15_lattice3(esk10_0,k1_xboole_0),k15_lattice3(esk10_0,X1))|r2_hidden(esk9_3(esk10_0,k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.44  cnf(c_0_60, plain, (k15_lattice3(X1,k6_domain_1(u1_struct_0(X1),X2))=X2|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.44  cnf(c_0_61, negated_conjecture, (k2_lattices(esk10_0,X1,k15_lattice3(esk10_0,X2))=X1|~r1_lattices(esk10_0,X1,k15_lattice3(esk10_0,X2))|~m1_subset_1(X1,u1_struct_0(esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53]), c_0_27])]), c_0_28])).
% 0.19/0.44  cnf(c_0_62, negated_conjecture, (r1_lattices(esk10_0,X1,k15_lattice3(esk10_0,X2))|~r3_lattices(esk10_0,X1,k15_lattice3(esk10_0,X2))|~m1_subset_1(X1,u1_struct_0(esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_51]), c_0_52]), c_0_53]), c_0_55]), c_0_27])]), c_0_28])).
% 0.19/0.44  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk4_2(esk10_0,k15_lattice3(esk10_0,X1)),u1_struct_0(esk10_0))|v13_lattices(esk10_0)|~l1_lattices(esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_51]), c_0_28])).
% 0.19/0.44  cnf(c_0_64, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.44  cnf(c_0_65, negated_conjecture, (k2_lattices(esk10_0,X1,k5_lattices(esk10_0))=X1|~r1_lattices(esk10_0,X1,k5_lattices(esk10_0))|~m1_subset_1(X1,u1_struct_0(esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_58]), c_0_52]), c_0_53]), c_0_27])]), c_0_28])).
% 0.19/0.44  cnf(c_0_66, negated_conjecture, (r1_lattices(esk10_0,X1,k5_lattices(esk10_0))|~r3_lattices(esk10_0,X1,k5_lattices(esk10_0))|~m1_subset_1(X1,u1_struct_0(esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_58]), c_0_52]), c_0_53]), c_0_55]), c_0_27])]), c_0_28])).
% 0.19/0.44  cnf(c_0_67, negated_conjecture, (r3_lattices(esk10_0,k15_lattice3(esk10_0,k1_xboole_0),k15_lattice3(esk10_0,X1))), inference(spm,[status(thm)],[c_0_29, c_0_59])).
% 0.19/0.44  cnf(c_0_68, negated_conjecture, (k15_lattice3(esk10_0,k6_domain_1(u1_struct_0(esk10_0),k5_lattices(esk10_0)))=k5_lattices(esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_58]), c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.44  cnf(c_0_69, negated_conjecture, (k2_lattices(esk10_0,X1,k15_lattice3(esk10_0,X2))=X1|~r3_lattices(esk10_0,X1,k15_lattice3(esk10_0,X2))|~m1_subset_1(X1,u1_struct_0(esk10_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.44  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk4_2(esk10_0,k15_lattice3(esk10_0,X1)),u1_struct_0(esk10_0))|v13_lattices(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_34]), c_0_27])])).
% 0.19/0.44  cnf(c_0_71, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_64]), c_0_33])).
% 0.19/0.44  cnf(c_0_72, negated_conjecture, (k2_lattices(esk10_0,X1,k5_lattices(esk10_0))=X1|~r3_lattices(esk10_0,X1,k5_lattices(esk10_0))|~m1_subset_1(X1,u1_struct_0(esk10_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.44  cnf(c_0_73, negated_conjecture, (r3_lattices(esk10_0,k15_lattice3(esk10_0,k1_xboole_0),k5_lattices(esk10_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.44  cnf(c_0_74, negated_conjecture, (v2_struct_0(esk10_0)|~v10_lattices(esk10_0)|~v13_lattices(esk10_0)|~l3_lattices(esk10_0)|k5_lattices(esk10_0)!=k15_lattice3(esk10_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  cnf(c_0_75, negated_conjecture, (k2_lattices(esk10_0,k15_lattice3(esk10_0,k1_xboole_0),k15_lattice3(esk10_0,X1))=k15_lattice3(esk10_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_67]), c_0_51])])).
% 0.19/0.44  cnf(c_0_76, negated_conjecture, (k15_lattice3(esk10_0,k6_domain_1(u1_struct_0(esk10_0),esk4_2(esk10_0,k15_lattice3(esk10_0,X1))))=esk4_2(esk10_0,k15_lattice3(esk10_0,X1))|v13_lattices(esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_70]), c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.44  cnf(c_0_77, negated_conjecture, (k2_lattices(esk10_0,k15_lattice3(esk10_0,X1),k5_lattices(esk10_0))=k5_lattices(esk10_0)|~v13_lattices(esk10_0)|~l1_lattices(esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_51]), c_0_28])).
% 0.19/0.44  cnf(c_0_78, negated_conjecture, (k2_lattices(esk10_0,k15_lattice3(esk10_0,k1_xboole_0),k5_lattices(esk10_0))=k15_lattice3(esk10_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_51])])).
% 0.19/0.44  cnf(c_0_79, negated_conjecture, (k5_lattices(esk10_0)!=k15_lattice3(esk10_0,k1_xboole_0)|~v13_lattices(esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_27]), c_0_26])]), c_0_28])).
% 0.19/0.44  fof(c_0_80, plain, ![X35, X36, X37]:((~v6_lattices(X35)|(~m1_subset_1(X36,u1_struct_0(X35))|(~m1_subset_1(X37,u1_struct_0(X35))|k2_lattices(X35,X36,X37)=k2_lattices(X35,X37,X36)))|(v2_struct_0(X35)|~l1_lattices(X35)))&((m1_subset_1(esk5_1(X35),u1_struct_0(X35))|v6_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))&((m1_subset_1(esk6_1(X35),u1_struct_0(X35))|v6_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))&(k2_lattices(X35,esk5_1(X35),esk6_1(X35))!=k2_lattices(X35,esk6_1(X35),esk5_1(X35))|v6_lattices(X35)|(v2_struct_0(X35)|~l1_lattices(X35)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 0.19/0.44  cnf(c_0_81, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk4_2(X1,X2))!=X2|k2_lattices(X1,esk4_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.44  cnf(c_0_82, negated_conjecture, (k2_lattices(esk10_0,k15_lattice3(esk10_0,k1_xboole_0),esk4_2(esk10_0,k15_lattice3(esk10_0,X1)))=k15_lattice3(esk10_0,k1_xboole_0)|v13_lattices(esk10_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.44  cnf(c_0_83, negated_conjecture, (~v13_lattices(esk10_0)|~l1_lattices(esk10_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])).
% 0.19/0.44  cnf(c_0_84, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.19/0.44  cnf(c_0_85, negated_conjecture, (k2_lattices(esk10_0,esk4_2(esk10_0,k15_lattice3(esk10_0,k1_xboole_0)),k15_lattice3(esk10_0,k1_xboole_0))!=k15_lattice3(esk10_0,k1_xboole_0)|~l1_lattices(esk10_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_51])]), c_0_28]), c_0_83])).
% 0.19/0.44  cnf(c_0_86, negated_conjecture, (k2_lattices(esk10_0,X1,esk4_2(esk10_0,k15_lattice3(esk10_0,X2)))=k2_lattices(esk10_0,esk4_2(esk10_0,k15_lattice3(esk10_0,X2)),X1)|~m1_subset_1(X1,u1_struct_0(esk10_0))|~l1_lattices(esk10_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_70]), c_0_55])]), c_0_28]), c_0_83])).
% 0.19/0.44  cnf(c_0_87, negated_conjecture, (k2_lattices(esk10_0,k15_lattice3(esk10_0,k1_xboole_0),esk4_2(esk10_0,k15_lattice3(esk10_0,k1_xboole_0)))!=k15_lattice3(esk10_0,k1_xboole_0)|~l1_lattices(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_51])])).
% 0.19/0.44  cnf(c_0_88, negated_conjecture, (~l1_lattices(esk10_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_82]), c_0_83])).
% 0.19/0.44  cnf(c_0_89, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_34]), c_0_27])]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 90
% 0.19/0.44  # Proof object clause steps            : 59
% 0.19/0.44  # Proof object formula steps           : 31
% 0.19/0.44  # Proof object conjectures             : 39
% 0.19/0.44  # Proof object clause conjectures      : 36
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 23
% 0.19/0.44  # Proof object initial formulas used   : 15
% 0.19/0.44  # Proof object generating inferences   : 33
% 0.19/0.44  # Proof object simplifying inferences  : 76
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 17
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 52
% 0.19/0.44  # Removed in clause preprocessing      : 1
% 0.19/0.44  # Initial clauses in saturation        : 51
% 0.19/0.44  # Processed clauses                    : 826
% 0.19/0.44  # ...of these trivial                  : 0
% 0.19/0.44  # ...subsumed                          : 376
% 0.19/0.44  # ...remaining for further processing  : 450
% 0.19/0.44  # Other redundant clauses eliminated   : 5
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 49
% 0.19/0.44  # Backward-rewritten                   : 1
% 0.19/0.44  # Generated clauses                    : 2107
% 0.19/0.44  # ...of the previous two non-trivial   : 1987
% 0.19/0.44  # Contextual simplify-reflections      : 35
% 0.19/0.44  # Paramodulations                      : 2102
% 0.19/0.44  # Factorizations                       : 0
% 0.19/0.44  # Equation resolutions                 : 5
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 344
% 0.19/0.44  #    Positive orientable unit clauses  : 24
% 0.19/0.44  #    Positive unorientable unit clauses: 0
% 0.19/0.44  #    Negative unit clauses             : 4
% 0.19/0.44  #    Non-unit-clauses                  : 316
% 0.19/0.44  # Current number of unprocessed clauses: 1238
% 0.19/0.44  # ...number of literals in the above   : 4921
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 101
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 18235
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 8707
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 412
% 0.19/0.44  # Unit Clause-clause subsumption calls : 530
% 0.19/0.44  # Rewrite failures with RHS unbound    : 0
% 0.19/0.44  # BW rewrite match attempts            : 8
% 0.19/0.44  # BW rewrite match successes           : 2
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 64964
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.111 s
% 0.19/0.44  # System time              : 0.008 s
% 0.19/0.44  # Total time               : 0.119 s
% 0.19/0.44  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
