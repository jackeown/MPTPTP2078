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
% DateTime   : Thu Dec  3 11:15:07 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  133 (3551 expanded)
%              Number of clauses        :   98 (1284 expanded)
%              Number of leaves         :   17 ( 889 expanded)
%              Depth                    :   35
%              Number of atoms          :  901 (26935 expanded)
%              Number of equality atoms :   78 (2260 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal clause size      :   40 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(fraenkel_a_2_5_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v4_lattice3(X2)
        & l3_lattices(X2) )
     => ( r2_hidden(X1,a_2_5_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ? [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
                & r3_lattices(X2,X4,X5)
                & r2_hidden(X5,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).

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

fof(dt_k15_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(d16_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r3_lattice3(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_hidden(X4,X3)
                   => r1_lattices(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

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

fof(t34_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( X2 = k16_lattice3(X1,X3)
            <=> ( r3_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r3_lattice3(X1,X4,X3)
                     => r3_lattices(X1,X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

fof(fraenkel_a_2_4_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & v4_lattice3(X2)
        & l3_lattices(X2)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( r2_hidden(X1,a_2_4_lattice3(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & r3_lattices(X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_4_lattice3)).

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

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

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

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

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

fof(c_0_17,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | ~ r1_tarski(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_18,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X60,X61,X62,X64] :
      ( ( m1_subset_1(esk11_3(X60,X61,X62),u1_struct_0(X60))
        | r3_lattices(X60,k15_lattice3(X60,X61),k15_lattice3(X60,X62))
        | v2_struct_0(X60)
        | ~ v10_lattices(X60)
        | ~ v4_lattice3(X60)
        | ~ l3_lattices(X60) )
      & ( r2_hidden(esk11_3(X60,X61,X62),X61)
        | r3_lattices(X60,k15_lattice3(X60,X61),k15_lattice3(X60,X62))
        | v2_struct_0(X60)
        | ~ v10_lattices(X60)
        | ~ v4_lattice3(X60)
        | ~ l3_lattices(X60) )
      & ( ~ m1_subset_1(X64,u1_struct_0(X60))
        | ~ r3_lattices(X60,esk11_3(X60,X61,X62),X64)
        | ~ r2_hidden(X64,X62)
        | r3_lattices(X60,k15_lattice3(X60,X61),k15_lattice3(X60,X62))
        | v2_struct_0(X60)
        | ~ v10_lattices(X60)
        | ~ v4_lattice3(X60)
        | ~ l3_lattices(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).

fof(c_0_22,plain,(
    ! [X42,X43,X44,X47,X48,X49] :
      ( ( m1_subset_1(esk8_3(X42,X43,X44),u1_struct_0(X43))
        | ~ r2_hidden(X42,a_2_5_lattice3(X43,X44))
        | v2_struct_0(X43)
        | ~ v10_lattices(X43)
        | ~ v4_lattice3(X43)
        | ~ l3_lattices(X43) )
      & ( X42 = esk8_3(X42,X43,X44)
        | ~ r2_hidden(X42,a_2_5_lattice3(X43,X44))
        | v2_struct_0(X43)
        | ~ v10_lattices(X43)
        | ~ v4_lattice3(X43)
        | ~ l3_lattices(X43) )
      & ( m1_subset_1(esk9_3(X42,X43,X44),u1_struct_0(X43))
        | ~ r2_hidden(X42,a_2_5_lattice3(X43,X44))
        | v2_struct_0(X43)
        | ~ v10_lattices(X43)
        | ~ v4_lattice3(X43)
        | ~ l3_lattices(X43) )
      & ( r3_lattices(X43,esk8_3(X42,X43,X44),esk9_3(X42,X43,X44))
        | ~ r2_hidden(X42,a_2_5_lattice3(X43,X44))
        | v2_struct_0(X43)
        | ~ v10_lattices(X43)
        | ~ v4_lattice3(X43)
        | ~ l3_lattices(X43) )
      & ( r2_hidden(esk9_3(X42,X43,X44),X44)
        | ~ r2_hidden(X42,a_2_5_lattice3(X43,X44))
        | v2_struct_0(X43)
        | ~ v10_lattices(X43)
        | ~ v4_lattice3(X43)
        | ~ l3_lattices(X43) )
      & ( ~ m1_subset_1(X48,u1_struct_0(X43))
        | X42 != X48
        | ~ m1_subset_1(X49,u1_struct_0(X43))
        | ~ r3_lattices(X43,X48,X49)
        | ~ r2_hidden(X49,X47)
        | r2_hidden(X42,a_2_5_lattice3(X43,X47))
        | v2_struct_0(X43)
        | ~ v10_lattices(X43)
        | ~ v4_lattice3(X43)
        | ~ l3_lattices(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_5_lattice3])])])])])])])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(esk11_3(X1,X2,X3),X2)
    | r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X56,X57] :
      ( ( X57 = k15_lattice3(X56,a_2_3_lattice3(X56,X57))
        | ~ m1_subset_1(X57,u1_struct_0(X56))
        | v2_struct_0(X56)
        | ~ v10_lattices(X56)
        | ~ v4_lattice3(X56)
        | ~ l3_lattices(X56) )
      & ( X57 = k16_lattice3(X56,a_2_4_lattice3(X56,X57))
        | ~ m1_subset_1(X57,u1_struct_0(X56))
        | v2_struct_0(X56)
        | ~ v10_lattices(X56)
        | ~ v4_lattice3(X56)
        | ~ l3_lattices(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X3,a_2_5_lattice3(X2,X5))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r3_lattices(X2,X1,X4)
    | ~ r2_hidden(X4,X5)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( r3_lattices(X1,k15_lattice3(X1,k1_xboole_0),k15_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( X1 = k15_lattice3(X2,a_2_3_lattice3(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_29,plain,(
    ! [X35,X36] :
      ( v2_struct_0(X35)
      | ~ l3_lattices(X35)
      | m1_subset_1(k15_lattice3(X35,X36),u1_struct_0(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_5_lattice3(X1,X3))
    | ~ r3_lattices(X1,X2,X4)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r3_lattices(X1,k15_lattice3(X1,k1_xboole_0),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( ( ~ r3_lattice3(X24,X25,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ r2_hidden(X27,X26)
        | r1_lattices(X24,X25,X27)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( m1_subset_1(esk4_3(X24,X25,X28),u1_struct_0(X24))
        | r3_lattice3(X24,X25,X28)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( r2_hidden(esk4_3(X24,X25,X28),X28)
        | r3_lattice3(X24,X25,X28)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) )
      & ( ~ r1_lattices(X24,X25,esk4_3(X24,X25,X28))
        | r3_lattice3(X24,X25,X28)
        | ~ m1_subset_1(X25,u1_struct_0(X24))
        | v2_struct_0(X24)
        | ~ l3_lattices(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k15_lattice3(X1,k1_xboole_0),a_2_5_lattice3(X1,X2))
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_36,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | r2_hidden(k15_lattice3(X1,k1_xboole_0),a_2_5_lattice3(X1,X4))
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X4) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_37,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X3)
    | r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_38,negated_conjecture,(
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

cnf(c_0_39,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | r2_hidden(k15_lattice3(X1,k1_xboole_0),a_2_5_lattice3(X1,X3))
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk12_0)
    & v10_lattices(esk12_0)
    & v4_lattice3(esk12_0)
    & l3_lattices(esk12_0)
    & ( v2_struct_0(esk12_0)
      | ~ v10_lattices(esk12_0)
      | ~ v13_lattices(esk12_0)
      | ~ l3_lattices(esk12_0)
      | k5_lattices(esk12_0) != k15_lattice3(esk12_0,k1_xboole_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_38])])])])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk8_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_5_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,plain,
    ( X1 = esk8_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_5_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_43,plain,
    ( r3_lattice3(X1,k15_lattice3(X1,X2),X3)
    | v2_struct_0(X1)
    | r2_hidden(k15_lattice3(X1,k1_xboole_0),a_2_5_lattice3(X1,X3))
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( v4_lattice3(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( v10_lattices(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( l3_lattices(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ r2_hidden(X1,a_2_5_lattice3(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r3_lattice3(esk12_0,k15_lattice3(esk12_0,X1),X2)
    | r2_hidden(k15_lattice3(esk12_0,k1_xboole_0),a_2_5_lattice3(esk12_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

fof(c_0_50,plain,(
    ! [X50,X51,X52,X53,X54] :
      ( ( r3_lattice3(X50,X51,X52)
        | X51 != k16_lattice3(X50,X52)
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50) )
      & ( ~ m1_subset_1(X53,u1_struct_0(X50))
        | ~ r3_lattice3(X50,X53,X52)
        | r3_lattices(X50,X53,X51)
        | X51 != k16_lattice3(X50,X52)
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50) )
      & ( m1_subset_1(esk10_3(X50,X51,X54),u1_struct_0(X50))
        | ~ r3_lattice3(X50,X51,X54)
        | X51 = k16_lattice3(X50,X54)
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50) )
      & ( r3_lattice3(X50,esk10_3(X50,X51,X54),X54)
        | ~ r3_lattice3(X50,X51,X54)
        | X51 = k16_lattice3(X50,X54)
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50) )
      & ( ~ r3_lattices(X50,esk10_3(X50,X51,X54),X51)
        | ~ r3_lattice3(X50,X51,X54)
        | X51 = k16_lattice3(X50,X54)
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | v2_struct_0(X50)
        | ~ v10_lattices(X50)
        | ~ v4_lattice3(X50)
        | ~ l3_lattices(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

cnf(c_0_51,negated_conjecture,
    ( r3_lattice3(esk12_0,k15_lattice3(esk12_0,X1),X2)
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

fof(c_0_52,plain,(
    ! [X37,X38,X39,X41] :
      ( ( m1_subset_1(esk7_3(X37,X38,X39),u1_struct_0(X38))
        | ~ r2_hidden(X37,a_2_4_lattice3(X38,X39))
        | v2_struct_0(X38)
        | ~ v10_lattices(X38)
        | ~ v4_lattice3(X38)
        | ~ l3_lattices(X38)
        | ~ m1_subset_1(X39,u1_struct_0(X38)) )
      & ( X37 = esk7_3(X37,X38,X39)
        | ~ r2_hidden(X37,a_2_4_lattice3(X38,X39))
        | v2_struct_0(X38)
        | ~ v10_lattices(X38)
        | ~ v4_lattice3(X38)
        | ~ l3_lattices(X38)
        | ~ m1_subset_1(X39,u1_struct_0(X38)) )
      & ( r3_lattices(X38,X39,esk7_3(X37,X38,X39))
        | ~ r2_hidden(X37,a_2_4_lattice3(X38,X39))
        | v2_struct_0(X38)
        | ~ v10_lattices(X38)
        | ~ v4_lattice3(X38)
        | ~ l3_lattices(X38)
        | ~ m1_subset_1(X39,u1_struct_0(X38)) )
      & ( ~ m1_subset_1(X41,u1_struct_0(X38))
        | X37 != X41
        | ~ r3_lattices(X38,X39,X41)
        | r2_hidden(X37,a_2_4_lattice3(X38,X39))
        | v2_struct_0(X38)
        | ~ v10_lattices(X38)
        | ~ v4_lattice3(X38)
        | ~ l3_lattices(X38)
        | ~ m1_subset_1(X39,u1_struct_0(X38)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_4_lattice3])])])])])])).

cnf(c_0_53,plain,
    ( r3_lattices(X2,X1,X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_lattice3(X2,X1,X3)
    | X4 != k16_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( r3_lattice3(esk12_0,X1,X2)
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_28]),c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_55,plain,
    ( r2_hidden(X3,a_2_4_lattice3(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r3_lattices(X2,X4,X1)
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( r3_lattices(esk12_0,X1,X2)
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | X2 != k16_lattice3(esk12_0,X3)
    | ~ m1_subset_1(X2,u1_struct_0(esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_57,plain,
    ( X1 = k16_lattice3(X2,a_2_4_lattice3(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_58,plain,
    ( r1_lattices(X1,X2,X4)
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_4_lattice3(X1,X3))
    | ~ r3_lattices(X1,X3,X2)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r3_lattices(esk12_0,X1,X2)
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_44]),c_0_45]),c_0_46])]),c_0_47])])).

cnf(c_0_61,negated_conjecture,
    ( r1_lattices(esk12_0,X1,X2)
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0))
    | ~ r2_hidden(X2,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_54]),c_0_46])]),c_0_47])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | r2_hidden(X1,a_2_4_lattice3(esk12_0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

fof(c_0_63,plain,(
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

cnf(c_0_64,negated_conjecture,
    ( r1_lattices(esk12_0,X1,X2)
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( r1_lattices(esk12_0,X1,X2)
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_32]),c_0_46])]),c_0_47])).

fof(c_0_67,plain,(
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

cnf(c_0_68,negated_conjecture,
    ( k2_lattices(esk12_0,X1,X2) = X1
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0))
    | ~ v9_lattices(esk12_0)
    | ~ v8_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_46])]),c_0_47])).

cnf(c_0_69,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( k2_lattices(esk12_0,X1,X2) = X1
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0))
    | ~ v8_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_71,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( k2_lattices(esk12_0,X1,X2) = X1
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_45]),c_0_46])]),c_0_47])).

fof(c_0_73,plain,(
    ! [X14] :
      ( v2_struct_0(X14)
      | ~ l1_lattices(X14)
      | m1_subset_1(k5_lattices(X14),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

cnf(c_0_74,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k16_lattice3(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_75,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_4_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_76,plain,
    ( X1 = esk7_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_4_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_77,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v6_lattices(X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | k2_lattices(X30,X31,X32) = k2_lattices(X30,X32,X31)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( m1_subset_1(esk5_1(X30),u1_struct_0(X30))
        | v6_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( m1_subset_1(esk6_1(X30),u1_struct_0(X30))
        | v6_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) )
      & ( k2_lattices(X30,esk5_1(X30),esk6_1(X30)) != k2_lattices(X30,esk6_1(X30),esk5_1(X30))
        | v6_lattices(X30)
        | v2_struct_0(X30)
        | ~ l1_lattices(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).

fof(c_0_78,plain,(
    ! [X15] :
      ( ( l1_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( l2_lattices(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_79,negated_conjecture,
    ( k2_lattices(esk12_0,X1,k15_lattice3(esk12_0,X2)) = X1
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_32]),c_0_46])]),c_0_47])).

cnf(c_0_80,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,plain,
    ( r3_lattice3(X1,X2,a_2_4_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_57])])).

cnf(c_0_82,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ v4_lattice3(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ r2_hidden(X1,a_2_4_lattice3(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_83,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_84,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_85,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( k2_lattices(esk12_0,k5_lattices(esk12_0),k15_lattice3(esk12_0,X1)) = k5_lattices(esk12_0)
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | ~ l1_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_47])).

cnf(c_0_87,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,esk4_3(X1,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_88,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X3,a_2_4_lattice3(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_81]),c_0_82])).

cnf(c_0_89,plain,
    ( k2_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( k2_lattices(esk12_0,k5_lattices(esk12_0),X1) = k5_lattices(esk12_0)
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0))
    | ~ l1_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_28]),c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_91,plain,
    ( r3_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk4_3(X1,X2,X3),a_2_4_lattice3(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_92,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_4_lattice3(X1,k15_lattice3(X1,k1_xboole_0)))
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_31]),c_0_32])).

cnf(c_0_93,negated_conjecture,
    ( k2_lattices(esk12_0,X1,k5_lattices(esk12_0)) = X1
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0))
    | ~ l1_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_80]),c_0_47])).

cnf(c_0_94,negated_conjecture,
    ( k2_lattices(esk12_0,X1,k5_lattices(esk12_0)) = k5_lattices(esk12_0)
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | ~ m1_subset_1(k5_lattices(esk12_0),u1_struct_0(esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0))
    | ~ l1_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_95,plain,
    ( r3_lattice3(X1,k15_lattice3(X1,k1_xboole_0),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(esk4_3(X1,k15_lattice3(X1,k1_xboole_0),X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_32])).

cnf(c_0_96,plain,
    ( m1_subset_1(esk11_3(X1,X2,X3),u1_struct_0(X1))
    | r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_97,negated_conjecture,
    ( k5_lattices(esk12_0) = X1
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | ~ m1_subset_1(k5_lattices(esk12_0),u1_struct_0(esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0))
    | ~ l1_lattices(esk12_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,plain,
    ( r3_lattice3(X1,k15_lattice3(X1,k1_xboole_0),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_35]),c_0_32])).

cnf(c_0_99,plain,
    ( r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | r2_hidden(k15_lattice3(X1,k1_xboole_0),a_2_5_lattice3(X1,X4))
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(esk11_3(X1,X2,X3),X4) ),
    inference(spm,[status(thm)],[c_0_34,c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( k5_lattices(esk12_0) = X1
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0))
    | ~ l1_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_80]),c_0_47])).

cnf(c_0_101,plain,
    ( r1_lattices(X1,k15_lattice3(X1,k1_xboole_0),X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_98]),c_0_32])).

cnf(c_0_102,plain,
    ( r2_hidden(esk9_3(X1,X2,X3),X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_5_lattice3(X2,X3))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_103,plain,
    ( r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))
    | v2_struct_0(X1)
    | r2_hidden(k15_lattice3(X1,k1_xboole_0),a_2_5_lattice3(X1,X2))
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_24])).

cnf(c_0_104,negated_conjecture,
    ( k5_lattices(esk12_0) = k15_lattice3(esk12_0,X1)
    | m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | ~ l1_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_32]),c_0_46])]),c_0_47])).

fof(c_0_105,plain,(
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

cnf(c_0_106,plain,
    ( r1_lattices(X1,k15_lattice3(X1,k1_xboole_0),X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v4_lattice3(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X3) ),
    inference(spm,[status(thm)],[c_0_101,c_0_92])).

cnf(c_0_107,plain,
    ( v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X2,a_2_5_lattice3(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( r3_lattices(esk12_0,k15_lattice3(esk12_0,X1),k15_lattice3(esk12_0,X2))
    | r2_hidden(k15_lattice3(esk12_0,k1_xboole_0),a_2_5_lattice3(esk12_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | m1_subset_1(k15_lattice3(esk12_0,X1),u1_struct_0(esk12_0))
    | ~ l1_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_104]),c_0_47])).

cnf(c_0_110,plain,
    ( k2_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != k5_lattices(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_111,plain,
    ( r1_lattices(X1,k15_lattice3(X1,k1_xboole_0),k5_lattices(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_lattice3(X1)
    | ~ v4_lattice3(X2)
    | ~ m1_subset_1(k5_lattices(X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_80]),c_0_85])).

cnf(c_0_112,negated_conjecture,
    ( r3_lattices(esk12_0,k15_lattice3(esk12_0,k1_xboole_0),k15_lattice3(esk12_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_113,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))
    | m1_subset_1(k15_lattice3(esk12_0,X1),u1_struct_0(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_85]),c_0_46])])).

cnf(c_0_114,plain,
    ( k2_lattices(X1,X2,k5_lattices(X1)) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_110]),c_0_80])).

cnf(c_0_115,plain,
    ( k2_lattices(X1,k15_lattice3(X1,k1_xboole_0),k5_lattices(X2)) = k15_lattice3(X1,k1_xboole_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v4_lattice3(X2)
    | ~ m1_subset_1(k5_lattices(X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_111]),c_0_71]),c_0_69]),c_0_32])).

fof(c_0_116,plain,(
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

cnf(c_0_117,negated_conjecture,
    ( r3_lattices(esk12_0,k15_lattice3(esk12_0,k1_xboole_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_28]),c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_118,negated_conjecture,
    ( m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0)) ),
    inference(ef,[status(thm)],[c_0_113])).

cnf(c_0_119,negated_conjecture,
    ( v2_struct_0(esk12_0)
    | ~ v10_lattices(esk12_0)
    | ~ v13_lattices(esk12_0)
    | ~ l3_lattices(esk12_0)
    | k5_lattices(esk12_0) != k15_lattice3(esk12_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_120,plain,
    ( k15_lattice3(X1,k1_xboole_0) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_85]),c_0_32])).

cnf(c_0_121,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | k2_lattices(X1,esk3_2(X1,X2),X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_122,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ r2_hidden(X3,a_2_4_lattice3(X1,X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_88]),c_0_71]),c_0_69]),c_0_82])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(X1,a_2_4_lattice3(esk12_0,k15_lattice3(esk12_0,k1_xboole_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_117]),c_0_44]),c_0_118]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_124,negated_conjecture,
    ( k5_lattices(esk12_0) != k15_lattice3(esk12_0,k1_xboole_0)
    | ~ v13_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_46]),c_0_45])]),c_0_47])).

cnf(c_0_125,plain,
    ( k15_lattice3(X1,k1_xboole_0) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ v4_lattice3(X1)
    | ~ v13_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_80]),c_0_85])).

cnf(c_0_126,plain,
    ( v13_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,esk3_2(X1,X2)) != X2
    | ~ m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_89]),c_0_85])).

cnf(c_0_127,negated_conjecture,
    ( k2_lattices(esk12_0,k15_lattice3(esk12_0,k1_xboole_0),X1) = k15_lattice3(esk12_0,k1_xboole_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_44]),c_0_118]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_128,negated_conjecture,
    ( ~ v13_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_129,negated_conjecture,
    ( ~ m1_subset_1(esk3_2(esk12_0,k15_lattice3(esk12_0,k1_xboole_0)),u1_struct_0(esk12_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_118]),c_0_45]),c_0_46])]),c_0_128]),c_0_47])).

cnf(c_0_130,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v13_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_131,negated_conjecture,
    ( ~ l1_lattices(esk12_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_118])]),c_0_128]),c_0_47])).

cnf(c_0_132,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_85]),c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:43:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.69/0.87  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.69/0.87  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.69/0.87  #
% 0.69/0.87  # Preprocessing time       : 0.032 s
% 0.69/0.87  # Presaturation interreduction done
% 0.69/0.87  
% 0.69/0.87  # Proof found!
% 0.69/0.87  # SZS status Theorem
% 0.69/0.87  # SZS output start CNFRefutation
% 0.69/0.87  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.69/0.87  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.69/0.87  fof(t48_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2, X3]:(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X2)&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>~((r3_lattices(X1,X4,X5)&r2_hidden(X5,X3)))))))=>r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_lattice3)).
% 0.69/0.87  fof(fraenkel_a_2_5_lattice3, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))=>(r2_hidden(X1,a_2_5_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r3_lattices(X2,X4,X5))&r2_hidden(X5,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_5_lattice3)).
% 0.69/0.87  fof(t45_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k15_lattice3(X1,a_2_3_lattice3(X1,X2))&X2=k16_lattice3(X1,a_2_4_lattice3(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_lattice3)).
% 0.69/0.87  fof(dt_k15_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 0.69/0.87  fof(d16_lattice3, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 0.69/0.87  fof(t50_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_lattice3)).
% 0.69/0.87  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 0.69/0.87  fof(fraenkel_a_2_4_lattice3, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X2))&v10_lattices(X2))&v4_lattice3(X2))&l3_lattices(X2))&m1_subset_1(X3,u1_struct_0(X2)))=>(r2_hidden(X1,a_2_4_lattice3(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&r3_lattices(X2,X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_4_lattice3)).
% 0.69/0.87  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 0.69/0.87  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.69/0.87  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.69/0.87  fof(d6_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v6_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_lattices)).
% 0.69/0.87  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.69/0.87  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 0.69/0.87  fof(d13_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_lattices)).
% 0.69/0.87  fof(c_0_17, plain, ![X7, X8]:(~r2_hidden(X7,X8)|~r1_tarski(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.69/0.87  fof(c_0_18, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.69/0.87  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.69/0.87  cnf(c_0_20, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.69/0.87  fof(c_0_21, plain, ![X60, X61, X62, X64]:((m1_subset_1(esk11_3(X60,X61,X62),u1_struct_0(X60))|r3_lattices(X60,k15_lattice3(X60,X61),k15_lattice3(X60,X62))|(v2_struct_0(X60)|~v10_lattices(X60)|~v4_lattice3(X60)|~l3_lattices(X60)))&((r2_hidden(esk11_3(X60,X61,X62),X61)|r3_lattices(X60,k15_lattice3(X60,X61),k15_lattice3(X60,X62))|(v2_struct_0(X60)|~v10_lattices(X60)|~v4_lattice3(X60)|~l3_lattices(X60)))&(~m1_subset_1(X64,u1_struct_0(X60))|(~r3_lattices(X60,esk11_3(X60,X61,X62),X64)|~r2_hidden(X64,X62))|r3_lattices(X60,k15_lattice3(X60,X61),k15_lattice3(X60,X62))|(v2_struct_0(X60)|~v10_lattices(X60)|~v4_lattice3(X60)|~l3_lattices(X60))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_lattice3])])])])])])).
% 0.69/0.87  fof(c_0_22, plain, ![X42, X43, X44, X47, X48, X49]:((((m1_subset_1(esk8_3(X42,X43,X44),u1_struct_0(X43))|~r2_hidden(X42,a_2_5_lattice3(X43,X44))|(v2_struct_0(X43)|~v10_lattices(X43)|~v4_lattice3(X43)|~l3_lattices(X43)))&(X42=esk8_3(X42,X43,X44)|~r2_hidden(X42,a_2_5_lattice3(X43,X44))|(v2_struct_0(X43)|~v10_lattices(X43)|~v4_lattice3(X43)|~l3_lattices(X43))))&(((m1_subset_1(esk9_3(X42,X43,X44),u1_struct_0(X43))|~r2_hidden(X42,a_2_5_lattice3(X43,X44))|(v2_struct_0(X43)|~v10_lattices(X43)|~v4_lattice3(X43)|~l3_lattices(X43)))&(r3_lattices(X43,esk8_3(X42,X43,X44),esk9_3(X42,X43,X44))|~r2_hidden(X42,a_2_5_lattice3(X43,X44))|(v2_struct_0(X43)|~v10_lattices(X43)|~v4_lattice3(X43)|~l3_lattices(X43))))&(r2_hidden(esk9_3(X42,X43,X44),X44)|~r2_hidden(X42,a_2_5_lattice3(X43,X44))|(v2_struct_0(X43)|~v10_lattices(X43)|~v4_lattice3(X43)|~l3_lattices(X43)))))&(~m1_subset_1(X48,u1_struct_0(X43))|X42!=X48|(~m1_subset_1(X49,u1_struct_0(X43))|~r3_lattices(X43,X48,X49)|~r2_hidden(X49,X47))|r2_hidden(X42,a_2_5_lattice3(X43,X47))|(v2_struct_0(X43)|~v10_lattices(X43)|~v4_lattice3(X43)|~l3_lattices(X43)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_5_lattice3])])])])])])])).
% 0.69/0.87  cnf(c_0_23, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.69/0.87  cnf(c_0_24, plain, (r2_hidden(esk11_3(X1,X2,X3),X2)|r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.69/0.87  fof(c_0_25, plain, ![X56, X57]:((X57=k15_lattice3(X56,a_2_3_lattice3(X56,X57))|~m1_subset_1(X57,u1_struct_0(X56))|(v2_struct_0(X56)|~v10_lattices(X56)|~v4_lattice3(X56)|~l3_lattices(X56)))&(X57=k16_lattice3(X56,a_2_4_lattice3(X56,X57))|~m1_subset_1(X57,u1_struct_0(X56))|(v2_struct_0(X56)|~v10_lattices(X56)|~v4_lattice3(X56)|~l3_lattices(X56)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t45_lattice3])])])])])).
% 0.69/0.87  cnf(c_0_26, plain, (r2_hidden(X3,a_2_5_lattice3(X2,X5))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~m1_subset_1(X4,u1_struct_0(X2))|~r3_lattices(X2,X1,X4)|~r2_hidden(X4,X5)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.69/0.87  cnf(c_0_27, plain, (r3_lattices(X1,k15_lattice3(X1,k1_xboole_0),k15_lattice3(X1,X2))|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.69/0.87  cnf(c_0_28, plain, (X1=k15_lattice3(X2,a_2_3_lattice3(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.69/0.87  fof(c_0_29, plain, ![X35, X36]:(v2_struct_0(X35)|~l3_lattices(X35)|m1_subset_1(k15_lattice3(X35,X36),u1_struct_0(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k15_lattice3])])])).
% 0.69/0.87  cnf(c_0_30, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_5_lattice3(X1,X3))|~r3_lattices(X1,X2,X4)|~v4_lattice3(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_26])).
% 0.69/0.87  cnf(c_0_31, plain, (r3_lattices(X1,k15_lattice3(X1,k1_xboole_0),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.69/0.87  cnf(c_0_32, plain, (v2_struct_0(X1)|m1_subset_1(k15_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.69/0.87  fof(c_0_33, plain, ![X24, X25, X26, X27, X28]:((~r3_lattice3(X24,X25,X26)|(~m1_subset_1(X27,u1_struct_0(X24))|(~r2_hidden(X27,X26)|r1_lattices(X24,X25,X27)))|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~l3_lattices(X24)))&((m1_subset_1(esk4_3(X24,X25,X28),u1_struct_0(X24))|r3_lattice3(X24,X25,X28)|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~l3_lattices(X24)))&((r2_hidden(esk4_3(X24,X25,X28),X28)|r3_lattice3(X24,X25,X28)|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~l3_lattices(X24)))&(~r1_lattices(X24,X25,esk4_3(X24,X25,X28))|r3_lattice3(X24,X25,X28)|~m1_subset_1(X25,u1_struct_0(X24))|(v2_struct_0(X24)|~l3_lattices(X24)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattice3])])])])])])])).
% 0.69/0.87  cnf(c_0_34, plain, (v2_struct_0(X1)|r2_hidden(k15_lattice3(X1,k1_xboole_0),a_2_5_lattice3(X1,X2))|~v4_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.69/0.87  cnf(c_0_35, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.69/0.87  cnf(c_0_36, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|r2_hidden(k15_lattice3(X1,k1_xboole_0),a_2_5_lattice3(X1,X4))|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(esk4_3(X1,X2,X3),X4)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.69/0.87  cnf(c_0_37, plain, (r2_hidden(esk4_3(X1,X2,X3),X3)|r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.69/0.87  fof(c_0_38, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))&k5_lattices(X1)=k15_lattice3(X1,k1_xboole_0)))), inference(assume_negation,[status(cth)],[t50_lattice3])).
% 0.69/0.87  cnf(c_0_39, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|r2_hidden(k15_lattice3(X1,k1_xboole_0),a_2_5_lattice3(X1,X3))|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.69/0.87  fof(c_0_40, negated_conjecture, ((((~v2_struct_0(esk12_0)&v10_lattices(esk12_0))&v4_lattice3(esk12_0))&l3_lattices(esk12_0))&(v2_struct_0(esk12_0)|~v10_lattices(esk12_0)|~v13_lattices(esk12_0)|~l3_lattices(esk12_0)|k5_lattices(esk12_0)!=k15_lattice3(esk12_0,k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_38])])])])).
% 0.69/0.87  cnf(c_0_41, plain, (m1_subset_1(esk8_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_5_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.69/0.87  cnf(c_0_42, plain, (X1=esk8_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_5_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.69/0.87  cnf(c_0_43, plain, (r3_lattice3(X1,k15_lattice3(X1,X2),X3)|v2_struct_0(X1)|r2_hidden(k15_lattice3(X1,k1_xboole_0),a_2_5_lattice3(X1,X3))|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_39, c_0_32])).
% 0.69/0.87  cnf(c_0_44, negated_conjecture, (v4_lattice3(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.69/0.87  cnf(c_0_45, negated_conjecture, (v10_lattices(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.69/0.87  cnf(c_0_46, negated_conjecture, (l3_lattices(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.69/0.87  cnf(c_0_47, negated_conjecture, (~v2_struct_0(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.69/0.87  cnf(c_0_48, plain, (m1_subset_1(X1,u1_struct_0(X2))|v2_struct_0(X2)|~v4_lattice3(X2)|~v10_lattices(X2)|~l3_lattices(X2)|~r2_hidden(X1,a_2_5_lattice3(X2,X3))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.69/0.87  cnf(c_0_49, negated_conjecture, (r3_lattice3(esk12_0,k15_lattice3(esk12_0,X1),X2)|r2_hidden(k15_lattice3(esk12_0,k1_xboole_0),a_2_5_lattice3(esk12_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])]), c_0_47])).
% 0.69/0.87  fof(c_0_50, plain, ![X50, X51, X52, X53, X54]:(((r3_lattice3(X50,X51,X52)|X51!=k16_lattice3(X50,X52)|~m1_subset_1(X51,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50)))&(~m1_subset_1(X53,u1_struct_0(X50))|(~r3_lattice3(X50,X53,X52)|r3_lattices(X50,X53,X51))|X51!=k16_lattice3(X50,X52)|~m1_subset_1(X51,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50))))&((m1_subset_1(esk10_3(X50,X51,X54),u1_struct_0(X50))|~r3_lattice3(X50,X51,X54)|X51=k16_lattice3(X50,X54)|~m1_subset_1(X51,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50)))&((r3_lattice3(X50,esk10_3(X50,X51,X54),X54)|~r3_lattice3(X50,X51,X54)|X51=k16_lattice3(X50,X54)|~m1_subset_1(X51,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50)))&(~r3_lattices(X50,esk10_3(X50,X51,X54),X51)|~r3_lattice3(X50,X51,X54)|X51=k16_lattice3(X50,X54)|~m1_subset_1(X51,u1_struct_0(X50))|(v2_struct_0(X50)|~v10_lattices(X50)|~v4_lattice3(X50)|~l3_lattices(X50)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.69/0.87  cnf(c_0_51, negated_conjecture, (r3_lattice3(esk12_0,k15_lattice3(esk12_0,X1),X2)|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_44]), c_0_45]), c_0_46])]), c_0_47])).
% 0.69/0.87  fof(c_0_52, plain, ![X37, X38, X39, X41]:((((m1_subset_1(esk7_3(X37,X38,X39),u1_struct_0(X38))|~r2_hidden(X37,a_2_4_lattice3(X38,X39))|(v2_struct_0(X38)|~v10_lattices(X38)|~v4_lattice3(X38)|~l3_lattices(X38)|~m1_subset_1(X39,u1_struct_0(X38))))&(X37=esk7_3(X37,X38,X39)|~r2_hidden(X37,a_2_4_lattice3(X38,X39))|(v2_struct_0(X38)|~v10_lattices(X38)|~v4_lattice3(X38)|~l3_lattices(X38)|~m1_subset_1(X39,u1_struct_0(X38)))))&(r3_lattices(X38,X39,esk7_3(X37,X38,X39))|~r2_hidden(X37,a_2_4_lattice3(X38,X39))|(v2_struct_0(X38)|~v10_lattices(X38)|~v4_lattice3(X38)|~l3_lattices(X38)|~m1_subset_1(X39,u1_struct_0(X38)))))&(~m1_subset_1(X41,u1_struct_0(X38))|X37!=X41|~r3_lattices(X38,X39,X41)|r2_hidden(X37,a_2_4_lattice3(X38,X39))|(v2_struct_0(X38)|~v10_lattices(X38)|~v4_lattice3(X38)|~l3_lattices(X38)|~m1_subset_1(X39,u1_struct_0(X38))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_4_lattice3])])])])])])).
% 0.69/0.87  cnf(c_0_53, plain, (r3_lattices(X2,X1,X4)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_lattice3(X2,X1,X3)|X4!=k16_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.69/0.87  cnf(c_0_54, negated_conjecture, (r3_lattice3(esk12_0,X1,X2)|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_28]), c_0_44]), c_0_45]), c_0_46])]), c_0_47])).
% 0.69/0.87  cnf(c_0_55, plain, (r2_hidden(X3,a_2_4_lattice3(X2,X4))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|X3!=X1|~r3_lattices(X2,X4,X1)|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~m1_subset_1(X4,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.69/0.87  cnf(c_0_56, negated_conjecture, (r3_lattices(esk12_0,X1,X2)|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|X2!=k16_lattice3(esk12_0,X3)|~m1_subset_1(X2,u1_struct_0(esk12_0))|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_44]), c_0_45]), c_0_46])]), c_0_47])).
% 0.69/0.87  cnf(c_0_57, plain, (X1=k16_lattice3(X2,a_2_4_lattice3(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.69/0.87  cnf(c_0_58, plain, (r1_lattices(X1,X2,X4)|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.69/0.87  cnf(c_0_59, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_4_lattice3(X1,X3))|~r3_lattices(X1,X3,X2)|~v4_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(er,[status(thm)],[c_0_55])).
% 0.69/0.87  cnf(c_0_60, negated_conjecture, (r3_lattices(esk12_0,X1,X2)|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|~m1_subset_1(X2,u1_struct_0(esk12_0))|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_44]), c_0_45]), c_0_46])]), c_0_47])])).
% 0.69/0.87  cnf(c_0_61, negated_conjecture, (r1_lattices(esk12_0,X1,X2)|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|~m1_subset_1(X2,u1_struct_0(esk12_0))|~m1_subset_1(X1,u1_struct_0(esk12_0))|~r2_hidden(X2,X3)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_54]), c_0_46])]), c_0_47])).
% 0.69/0.87  cnf(c_0_62, negated_conjecture, (m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|r2_hidden(X1,a_2_4_lattice3(esk12_0,X2))|~m1_subset_1(X2,u1_struct_0(esk12_0))|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_44]), c_0_45]), c_0_46])]), c_0_47])).
% 0.69/0.87  fof(c_0_63, plain, ![X16, X17, X18]:((~r1_lattices(X16,X17,X18)|k2_lattices(X16,X17,X18)=X17|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v8_lattices(X16)|~v9_lattices(X16)|~l3_lattices(X16)))&(k2_lattices(X16,X17,X18)!=X17|r1_lattices(X16,X17,X18)|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v8_lattices(X16)|~v9_lattices(X16)|~l3_lattices(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.69/0.87  cnf(c_0_64, negated_conjecture, (r1_lattices(esk12_0,X1,X2)|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|~m1_subset_1(X2,u1_struct_0(esk12_0))|~m1_subset_1(X1,u1_struct_0(esk12_0))|~m1_subset_1(X3,u1_struct_0(esk12_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.69/0.87  cnf(c_0_65, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.69/0.87  cnf(c_0_66, negated_conjecture, (r1_lattices(esk12_0,X1,X2)|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|~m1_subset_1(X2,u1_struct_0(esk12_0))|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_32]), c_0_46])]), c_0_47])).
% 0.69/0.87  fof(c_0_67, plain, ![X9]:(((((((~v2_struct_0(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9))&(v4_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v5_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v6_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v7_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v8_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9)))&(v9_lattices(X9)|(v2_struct_0(X9)|~v10_lattices(X9))|~l3_lattices(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.69/0.87  cnf(c_0_68, negated_conjecture, (k2_lattices(esk12_0,X1,X2)=X1|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|~m1_subset_1(X2,u1_struct_0(esk12_0))|~m1_subset_1(X1,u1_struct_0(esk12_0))|~v9_lattices(esk12_0)|~v8_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_46])]), c_0_47])).
% 0.69/0.87  cnf(c_0_69, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.69/0.87  cnf(c_0_70, negated_conjecture, (k2_lattices(esk12_0,X1,X2)=X1|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|~m1_subset_1(X2,u1_struct_0(esk12_0))|~m1_subset_1(X1,u1_struct_0(esk12_0))|~v8_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_45]), c_0_46])]), c_0_47])).
% 0.69/0.87  cnf(c_0_71, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.69/0.87  cnf(c_0_72, negated_conjecture, (k2_lattices(esk12_0,X1,X2)=X1|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|~m1_subset_1(X2,u1_struct_0(esk12_0))|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_45]), c_0_46])]), c_0_47])).
% 0.69/0.87  fof(c_0_73, plain, ![X14]:(v2_struct_0(X14)|~l1_lattices(X14)|m1_subset_1(k5_lattices(X14),u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.69/0.87  cnf(c_0_74, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|X2!=k16_lattice3(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.69/0.87  cnf(c_0_75, plain, (m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_4_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.69/0.87  cnf(c_0_76, plain, (X1=esk7_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_4_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.69/0.87  fof(c_0_77, plain, ![X30, X31, X32]:((~v6_lattices(X30)|(~m1_subset_1(X31,u1_struct_0(X30))|(~m1_subset_1(X32,u1_struct_0(X30))|k2_lattices(X30,X31,X32)=k2_lattices(X30,X32,X31)))|(v2_struct_0(X30)|~l1_lattices(X30)))&((m1_subset_1(esk5_1(X30),u1_struct_0(X30))|v6_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))&((m1_subset_1(esk6_1(X30),u1_struct_0(X30))|v6_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))&(k2_lattices(X30,esk5_1(X30),esk6_1(X30))!=k2_lattices(X30,esk6_1(X30),esk5_1(X30))|v6_lattices(X30)|(v2_struct_0(X30)|~l1_lattices(X30)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_lattices])])])])])])).
% 0.69/0.87  fof(c_0_78, plain, ![X15]:((l1_lattices(X15)|~l3_lattices(X15))&(l2_lattices(X15)|~l3_lattices(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.69/0.87  cnf(c_0_79, negated_conjecture, (k2_lattices(esk12_0,X1,k15_lattice3(esk12_0,X2))=X1|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_32]), c_0_46])]), c_0_47])).
% 0.69/0.87  cnf(c_0_80, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.69/0.87  cnf(c_0_81, plain, (r3_lattice3(X1,X2,a_2_4_lattice3(X1,X2))|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_57])])).
% 0.69/0.87  cnf(c_0_82, plain, (m1_subset_1(X1,u1_struct_0(X2))|v2_struct_0(X2)|~v4_lattice3(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~v10_lattices(X2)|~l3_lattices(X2)|~r2_hidden(X1,a_2_4_lattice3(X2,X3))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.69/0.87  cnf(c_0_83, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~v6_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.69/0.87  cnf(c_0_84, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.69/0.87  cnf(c_0_85, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.69/0.87  cnf(c_0_86, negated_conjecture, (k2_lattices(esk12_0,k5_lattices(esk12_0),k15_lattice3(esk12_0,X1))=k5_lattices(esk12_0)|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|~l1_lattices(esk12_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_47])).
% 0.69/0.87  cnf(c_0_87, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,esk4_3(X1,X2,X3))|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.69/0.87  cnf(c_0_88, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X3,a_2_4_lattice3(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_81]), c_0_82])).
% 0.69/0.87  cnf(c_0_89, plain, (k2_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 0.69/0.87  cnf(c_0_90, negated_conjecture, (k2_lattices(esk12_0,k5_lattices(esk12_0),X1)=k5_lattices(esk12_0)|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|~m1_subset_1(X1,u1_struct_0(esk12_0))|~l1_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_28]), c_0_44]), c_0_45]), c_0_46])]), c_0_47])).
% 0.69/0.87  cnf(c_0_91, plain, (r3_lattice3(X1,X2,X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(esk4_3(X1,X2,X3),a_2_4_lattice3(X1,X2))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.69/0.87  cnf(c_0_92, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_4_lattice3(X1,k15_lattice3(X1,k1_xboole_0)))|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_31]), c_0_32])).
% 0.69/0.87  cnf(c_0_93, negated_conjecture, (k2_lattices(esk12_0,X1,k5_lattices(esk12_0))=X1|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|~m1_subset_1(X1,u1_struct_0(esk12_0))|~l1_lattices(esk12_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_80]), c_0_47])).
% 0.69/0.87  cnf(c_0_94, negated_conjecture, (k2_lattices(esk12_0,X1,k5_lattices(esk12_0))=k5_lattices(esk12_0)|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|~m1_subset_1(k5_lattices(esk12_0),u1_struct_0(esk12_0))|~m1_subset_1(X1,u1_struct_0(esk12_0))|~l1_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_45]), c_0_46])]), c_0_47])).
% 0.69/0.87  cnf(c_0_95, plain, (r3_lattice3(X1,k15_lattice3(X1,k1_xboole_0),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(esk4_3(X1,k15_lattice3(X1,k1_xboole_0),X2),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_32])).
% 0.69/0.87  cnf(c_0_96, plain, (m1_subset_1(esk11_3(X1,X2,X3),u1_struct_0(X1))|r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|~v10_lattices(X1)|~v4_lattice3(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.69/0.87  cnf(c_0_97, negated_conjecture, (k5_lattices(esk12_0)=X1|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|~m1_subset_1(k5_lattices(esk12_0),u1_struct_0(esk12_0))|~m1_subset_1(X1,u1_struct_0(esk12_0))|~l1_lattices(esk12_0)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.69/0.87  cnf(c_0_98, plain, (r3_lattice3(X1,k15_lattice3(X1,k1_xboole_0),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_35]), c_0_32])).
% 0.69/0.87  cnf(c_0_99, plain, (r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|r2_hidden(k15_lattice3(X1,k1_xboole_0),a_2_5_lattice3(X1,X4))|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(esk11_3(X1,X2,X3),X4)), inference(spm,[status(thm)],[c_0_34, c_0_96])).
% 0.69/0.87  cnf(c_0_100, negated_conjecture, (k5_lattices(esk12_0)=X1|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|~m1_subset_1(X1,u1_struct_0(esk12_0))|~l1_lattices(esk12_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_80]), c_0_47])).
% 0.69/0.87  cnf(c_0_101, plain, (r1_lattices(X1,k15_lattice3(X1,k1_xboole_0),X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_98]), c_0_32])).
% 0.69/0.87  cnf(c_0_102, plain, (r2_hidden(esk9_3(X1,X2,X3),X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_5_lattice3(X2,X3))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.69/0.87  cnf(c_0_103, plain, (r3_lattices(X1,k15_lattice3(X1,X2),k15_lattice3(X1,X3))|v2_struct_0(X1)|r2_hidden(k15_lattice3(X1,k1_xboole_0),a_2_5_lattice3(X1,X2))|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_99, c_0_24])).
% 0.69/0.87  cnf(c_0_104, negated_conjecture, (k5_lattices(esk12_0)=k15_lattice3(esk12_0,X1)|m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|~l1_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_32]), c_0_46])]), c_0_47])).
% 0.69/0.87  fof(c_0_105, plain, ![X10, X11, X12]:(((k2_lattices(X10,X11,X12)=X11|~m1_subset_1(X12,u1_struct_0(X10))|X11!=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10)))&(k2_lattices(X10,X12,X11)=X11|~m1_subset_1(X12,u1_struct_0(X10))|X11!=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10))))&((m1_subset_1(esk1_2(X10,X11),u1_struct_0(X10))|X11=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10)))&(k2_lattices(X10,X11,esk1_2(X10,X11))!=X11|k2_lattices(X10,esk1_2(X10,X11),X11)!=X11|X11=k5_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~v13_lattices(X10)|(v2_struct_0(X10)|~l1_lattices(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.69/0.87  cnf(c_0_106, plain, (r1_lattices(X1,k15_lattice3(X1,k1_xboole_0),X2)|v2_struct_0(X3)|v2_struct_0(X1)|~v4_lattice3(X1)|~v4_lattice3(X3)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X3))|~v10_lattices(X1)|~v10_lattices(X3)|~l3_lattices(X1)|~l3_lattices(X3)), inference(spm,[status(thm)],[c_0_101, c_0_92])).
% 0.69/0.87  cnf(c_0_107, plain, (v2_struct_0(X1)|~v4_lattice3(X1)|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X2,a_2_5_lattice3(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_23, c_0_102])).
% 0.69/0.87  cnf(c_0_108, negated_conjecture, (r3_lattices(esk12_0,k15_lattice3(esk12_0,X1),k15_lattice3(esk12_0,X2))|r2_hidden(k15_lattice3(esk12_0,k1_xboole_0),a_2_5_lattice3(esk12_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_44]), c_0_45]), c_0_46])]), c_0_47])).
% 0.69/0.87  cnf(c_0_109, negated_conjecture, (m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|m1_subset_1(k15_lattice3(esk12_0,X1),u1_struct_0(esk12_0))|~l1_lattices(esk12_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_104]), c_0_47])).
% 0.69/0.87  cnf(c_0_110, plain, (k2_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|X3!=k5_lattices(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.69/0.87  cnf(c_0_111, plain, (r1_lattices(X1,k15_lattice3(X1,k1_xboole_0),k5_lattices(X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v4_lattice3(X1)|~v4_lattice3(X2)|~m1_subset_1(k5_lattices(X2),u1_struct_0(X1))|~v10_lattices(X1)|~v10_lattices(X2)|~l3_lattices(X1)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_80]), c_0_85])).
% 0.69/0.87  cnf(c_0_112, negated_conjecture, (r3_lattices(esk12_0,k15_lattice3(esk12_0,k1_xboole_0),k15_lattice3(esk12_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_44]), c_0_45]), c_0_46])]), c_0_47])).
% 0.69/0.87  cnf(c_0_113, negated_conjecture, (m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))|m1_subset_1(k15_lattice3(esk12_0,X1),u1_struct_0(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_85]), c_0_46])])).
% 0.69/0.87  cnf(c_0_114, plain, (k2_lattices(X1,X2,k5_lattices(X1))=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_110]), c_0_80])).
% 0.69/0.87  cnf(c_0_115, plain, (k2_lattices(X1,k15_lattice3(X1,k1_xboole_0),k5_lattices(X2))=k15_lattice3(X1,k1_xboole_0)|v2_struct_0(X2)|v2_struct_0(X1)|~v4_lattice3(X1)|~v4_lattice3(X2)|~m1_subset_1(k5_lattices(X2),u1_struct_0(X1))|~v10_lattices(X1)|~v10_lattices(X2)|~l3_lattices(X1)|~l3_lattices(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_111]), c_0_71]), c_0_69]), c_0_32])).
% 0.69/0.87  fof(c_0_116, plain, ![X19, X21, X22]:(((m1_subset_1(esk2_1(X19),u1_struct_0(X19))|~v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))&((k2_lattices(X19,esk2_1(X19),X21)=esk2_1(X19)|~m1_subset_1(X21,u1_struct_0(X19))|~v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))&(k2_lattices(X19,X21,esk2_1(X19))=esk2_1(X19)|~m1_subset_1(X21,u1_struct_0(X19))|~v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))))&((m1_subset_1(esk3_2(X19,X22),u1_struct_0(X19))|~m1_subset_1(X22,u1_struct_0(X19))|v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19)))&(k2_lattices(X19,X22,esk3_2(X19,X22))!=X22|k2_lattices(X19,esk3_2(X19,X22),X22)!=X22|~m1_subset_1(X22,u1_struct_0(X19))|v13_lattices(X19)|(v2_struct_0(X19)|~l1_lattices(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_lattices])])])])])])).
% 0.69/0.87  cnf(c_0_117, negated_conjecture, (r3_lattices(esk12_0,k15_lattice3(esk12_0,k1_xboole_0),X1)|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_28]), c_0_44]), c_0_45]), c_0_46])]), c_0_47])).
% 0.69/0.87  cnf(c_0_118, negated_conjecture, (m1_subset_1(k15_lattice3(esk12_0,k1_xboole_0),u1_struct_0(esk12_0))), inference(ef,[status(thm)],[c_0_113])).
% 0.69/0.87  cnf(c_0_119, negated_conjecture, (v2_struct_0(esk12_0)|~v10_lattices(esk12_0)|~v13_lattices(esk12_0)|~l3_lattices(esk12_0)|k5_lattices(esk12_0)!=k15_lattice3(esk12_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.69/0.87  cnf(c_0_120, plain, (k15_lattice3(X1,k1_xboole_0)=k5_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~v13_lattices(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_85]), c_0_32])).
% 0.69/0.87  cnf(c_0_121, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|k2_lattices(X1,esk3_2(X1,X2),X2)!=X2|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_116])).
% 0.69/0.87  cnf(c_0_122, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~v4_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~r2_hidden(X3,a_2_4_lattice3(X1,X2))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_88]), c_0_71]), c_0_69]), c_0_82])).
% 0.69/0.87  cnf(c_0_123, negated_conjecture, (r2_hidden(X1,a_2_4_lattice3(esk12_0,k15_lattice3(esk12_0,k1_xboole_0)))|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_117]), c_0_44]), c_0_118]), c_0_45]), c_0_46])]), c_0_47])).
% 0.69/0.87  cnf(c_0_124, negated_conjecture, (k5_lattices(esk12_0)!=k15_lattice3(esk12_0,k1_xboole_0)|~v13_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_46]), c_0_45])]), c_0_47])).
% 0.69/0.87  cnf(c_0_125, plain, (k15_lattice3(X1,k1_xboole_0)=k5_lattices(X1)|v2_struct_0(X1)|~v4_lattice3(X1)|~v13_lattices(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_80]), c_0_85])).
% 0.69/0.87  cnf(c_0_126, plain, (v13_lattices(X1)|v2_struct_0(X1)|k2_lattices(X1,X2,esk3_2(X1,X2))!=X2|~m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_89]), c_0_85])).
% 0.69/0.87  cnf(c_0_127, negated_conjecture, (k2_lattices(esk12_0,k15_lattice3(esk12_0,k1_xboole_0),X1)=k15_lattice3(esk12_0,k1_xboole_0)|~m1_subset_1(X1,u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_44]), c_0_118]), c_0_45]), c_0_46])]), c_0_47])).
% 0.69/0.87  cnf(c_0_128, negated_conjecture, (~v13_lattices(esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_44]), c_0_45]), c_0_46])]), c_0_47])).
% 0.69/0.87  cnf(c_0_129, negated_conjecture, (~m1_subset_1(esk3_2(esk12_0,k15_lattice3(esk12_0,k1_xboole_0)),u1_struct_0(esk12_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_118]), c_0_45]), c_0_46])]), c_0_128]), c_0_47])).
% 0.69/0.87  cnf(c_0_130, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v13_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_116])).
% 0.69/0.87  cnf(c_0_131, negated_conjecture, (~l1_lattices(esk12_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_118])]), c_0_128]), c_0_47])).
% 0.69/0.87  cnf(c_0_132, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_85]), c_0_46])]), ['proof']).
% 0.69/0.87  # SZS output end CNFRefutation
% 0.69/0.87  # Proof object total steps             : 133
% 0.69/0.87  # Proof object clause steps            : 98
% 0.69/0.87  # Proof object formula steps           : 35
% 0.69/0.87  # Proof object conjectures             : 41
% 0.69/0.87  # Proof object clause conjectures      : 38
% 0.69/0.87  # Proof object formula conjectures     : 3
% 0.69/0.87  # Proof object initial clauses used    : 35
% 0.69/0.87  # Proof object initial formulas used   : 17
% 0.69/0.87  # Proof object generating inferences   : 60
% 0.69/0.87  # Proof object simplifying inferences  : 137
% 0.69/0.87  # Training examples: 0 positive, 0 negative
% 0.69/0.87  # Parsed axioms                        : 18
% 0.69/0.87  # Removed by relevancy pruning/SinE    : 0
% 0.69/0.87  # Initial clauses                      : 59
% 0.69/0.87  # Removed in clause preprocessing      : 1
% 0.69/0.87  # Initial clauses in saturation        : 58
% 0.69/0.87  # Processed clauses                    : 3788
% 0.69/0.87  # ...of these trivial                  : 8
% 0.69/0.87  # ...subsumed                          : 2713
% 0.69/0.87  # ...remaining for further processing  : 1067
% 0.69/0.87  # Other redundant clauses eliminated   : 17
% 0.69/0.87  # Clauses deleted for lack of memory   : 0
% 0.69/0.87  # Backward-subsumed                    : 179
% 0.69/0.87  # Backward-rewritten                   : 45
% 0.69/0.87  # Generated clauses                    : 17332
% 0.69/0.87  # ...of the previous two non-trivial   : 16398
% 0.69/0.87  # Contextual simplify-reflections      : 93
% 0.69/0.87  # Paramodulations                      : 17270
% 0.69/0.87  # Factorizations                       : 2
% 0.69/0.87  # Equation resolutions                 : 55
% 0.69/0.87  # Propositional unsat checks           : 0
% 0.69/0.87  #    Propositional check models        : 0
% 0.69/0.87  #    Propositional check unsatisfiable : 0
% 0.69/0.87  #    Propositional clauses             : 0
% 0.69/0.87  #    Propositional clauses after purity: 0
% 0.69/0.87  #    Propositional unsat core size     : 0
% 0.69/0.87  #    Propositional preprocessing time  : 0.000
% 0.69/0.87  #    Propositional encoding time       : 0.000
% 0.69/0.87  #    Propositional solver time         : 0.000
% 0.69/0.87  #    Success case prop preproc time    : 0.000
% 0.69/0.87  #    Success case prop encoding time   : 0.000
% 0.69/0.87  #    Success case prop solver time     : 0.000
% 0.69/0.87  # Current number of processed clauses  : 778
% 0.69/0.87  #    Positive orientable unit clauses  : 12
% 0.69/0.87  #    Positive unorientable unit clauses: 0
% 0.69/0.87  #    Negative unit clauses             : 5
% 0.69/0.87  #    Non-unit-clauses                  : 761
% 0.69/0.87  # Current number of unprocessed clauses: 11764
% 0.69/0.87  # ...number of literals in the above   : 77029
% 0.69/0.87  # Current number of archived formulas  : 0
% 0.69/0.87  # Current number of archived clauses   : 287
% 0.69/0.87  # Clause-clause subsumption calls (NU) : 233520
% 0.69/0.87  # Rec. Clause-clause subsumption calls : 22041
% 0.69/0.87  # Non-unit clause-clause subsumptions  : 2230
% 0.69/0.87  # Unit Clause-clause subsumption calls : 717
% 0.69/0.87  # Rewrite failures with RHS unbound    : 0
% 0.69/0.87  # BW rewrite match attempts            : 30
% 0.69/0.87  # BW rewrite match successes           : 5
% 0.69/0.87  # Condensation attempts                : 0
% 0.69/0.87  # Condensation successes               : 0
% 0.69/0.87  # Termbank termtop insertions          : 535545
% 0.69/0.87  
% 0.69/0.87  # -------------------------------------------------
% 0.69/0.87  # User time                : 0.511 s
% 0.69/0.87  # System time              : 0.015 s
% 0.69/0.87  # Total time               : 0.526 s
% 0.69/0.87  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
