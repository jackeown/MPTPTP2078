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
% DateTime   : Thu Dec  3 11:16:26 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  114 (1647 expanded)
%              Number of clauses        :   79 ( 556 expanded)
%              Number of leaves         :   16 ( 532 expanded)
%              Depth                    :   20
%              Number of atoms          :  527 (16696 expanded)
%              Number of equality atoms :   43 (1577 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( ! [X4] :
                      ( ( v1_finset_1(X4)
                        & m1_subset_1(X4,k1_zfmisc_1(X2)) )
                     => ( X4 != k1_xboole_0
                       => r1_yellow_0(X1,X4) ) )
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ~ ( r2_hidden(X4,X3)
                          & ! [X5] :
                              ( ( v1_finset_1(X5)
                                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                             => ~ ( r1_yellow_0(X1,X5)
                                  & X4 = k1_yellow_0(X1,X5) ) ) ) )
                  & ! [X4] :
                      ( ( v1_finset_1(X4)
                        & m1_subset_1(X4,k1_zfmisc_1(X2)) )
                     => ( X4 != k1_xboole_0
                       => r2_hidden(k1_yellow_0(X1,X4),X3) ) ) )
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                    <=> r2_lattice3(X1,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_waybel_0)).

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(t9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => ! [X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ( ( r1_lattice3(X1,X3,X4)
                 => r1_lattice3(X1,X2,X4) )
                & ( r2_lattice3(X1,X3,X4)
                 => r2_lattice3(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

fof(d9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_yellow_0(X1,X2)
           => ( X3 = k1_yellow_0(X1,X2)
            <=> ( r2_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(fc1_finset_1,axiom,(
    ! [X1] : v1_finset_1(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t4_yellow_0,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
               => ! [X4] :
                    ( ( r1_lattice3(X1,X4,X3)
                     => r1_lattice3(X1,X4,X2) )
                    & ( r2_lattice3(X1,X4,X2)
                     => r2_lattice3(X1,X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_0)).

fof(t8_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_lattice3(X1,k2_tarski(X3,X4),X2)
                     => ( r1_orders_2(X1,X2,X3)
                        & r1_orders_2(X1,X2,X4) ) )
                    & ( ( r1_orders_2(X1,X2,X3)
                        & r1_orders_2(X1,X2,X4) )
                     => r1_lattice3(X1,k2_tarski(X3,X4),X2) )
                    & ( r2_lattice3(X1,k2_tarski(X3,X4),X2)
                     => ( r1_orders_2(X1,X3,X2)
                        & r1_orders_2(X1,X4,X2) ) )
                    & ( ( r1_orders_2(X1,X3,X2)
                        & r1_orders_2(X1,X4,X2) )
                     => r2_lattice3(X1,k2_tarski(X3,X4),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_0)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_14,plain,(
    ! [X1,X2,X3] :
      ( epred2_3(X3,X2,X1)
    <=> ( ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r1_yellow_0(X1,X4) ) )
        & ! [X4] :
            ( m1_subset_1(X4,u1_struct_0(X1))
           => ~ ( r2_hidden(X4,X3)
                & ! [X5] :
                    ( ( v1_finset_1(X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                   => ~ ( r1_yellow_0(X1,X5)
                        & X4 = k1_yellow_0(X1,X5) ) ) ) )
        & ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_hidden(k1_yellow_0(X1,X4),X3) ) ) ) ) ),
    introduced(definition)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( epred2_3(X3,X2,X1)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X2,X4)
                      <=> r2_lattice3(X1,X3,X4) ) ) ) ) ) ) ),
    inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t52_waybel_0]),c_0_14])).

fof(c_0_16,plain,(
    ! [X1,X2,X3] :
      ( epred2_3(X3,X2,X1)
     => ( ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r1_yellow_0(X1,X4) ) )
        & ! [X4] :
            ( m1_subset_1(X4,u1_struct_0(X1))
           => ~ ( r2_hidden(X4,X3)
                & ! [X5] :
                    ( ( v1_finset_1(X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                   => ~ ( r1_yellow_0(X1,X5)
                        & X4 = k1_yellow_0(X1,X5) ) ) ) )
        & ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_hidden(k1_yellow_0(X1,X4),X3) ) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ r2_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ r2_hidden(X19,X17)
        | r1_orders_2(X16,X19,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( m1_subset_1(esk1_3(X16,X17,X18),u1_struct_0(X16))
        | r2_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( r2_hidden(esk1_3(X16,X17,X18),X17)
        | r2_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( ~ r1_orders_2(X16,esk1_3(X16,X17,X18),X18)
        | r2_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v4_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & epred2_3(esk5_0,esk4_0,esk3_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & ( ~ r2_lattice3(esk3_0,esk4_0,esk6_0)
      | ~ r2_lattice3(esk3_0,esk5_0,esk6_0) )
    & ( r2_lattice3(esk3_0,esk4_0,esk6_0)
      | r2_lattice3(esk3_0,esk5_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_19,plain,(
    ! [X48,X49,X50,X51,X52,X54] :
      ( ( ~ v1_finset_1(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X49))
        | X51 = k1_xboole_0
        | r1_yellow_0(X48,X51)
        | ~ epred2_3(X50,X49,X48) )
      & ( v1_finset_1(esk7_4(X48,X49,X50,X52))
        | ~ r2_hidden(X52,X50)
        | ~ m1_subset_1(X52,u1_struct_0(X48))
        | ~ epred2_3(X50,X49,X48) )
      & ( m1_subset_1(esk7_4(X48,X49,X50,X52),k1_zfmisc_1(X49))
        | ~ r2_hidden(X52,X50)
        | ~ m1_subset_1(X52,u1_struct_0(X48))
        | ~ epred2_3(X50,X49,X48) )
      & ( r1_yellow_0(X48,esk7_4(X48,X49,X50,X52))
        | ~ r2_hidden(X52,X50)
        | ~ m1_subset_1(X52,u1_struct_0(X48))
        | ~ epred2_3(X50,X49,X48) )
      & ( X52 = k1_yellow_0(X48,esk7_4(X48,X49,X50,X52))
        | ~ r2_hidden(X52,X50)
        | ~ m1_subset_1(X52,u1_struct_0(X48))
        | ~ epred2_3(X50,X49,X48) )
      & ( ~ v1_finset_1(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X49))
        | X54 = k1_xboole_0
        | r2_hidden(k1_yellow_0(X48,X54),X50)
        | ~ epred2_3(X50,X49,X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( X1 = k1_yellow_0(X2,esk7_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred2_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_25,plain,
    ( r1_yellow_0(X1,esk7_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred2_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X2))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred2_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,X3,esk6_0))) = esk1_3(esk3_0,X3,esk6_0)
    | r2_lattice3(esk3_0,X3,esk6_0)
    | ~ epred2_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,X3,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( epred2_3(esk5_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,X3,esk6_0)))
    | r2_lattice3(esk3_0,X3,esk6_0)
    | ~ epred2_3(X2,X1,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,X3,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

fof(c_0_31,plain,(
    ! [X36,X37,X38,X39] :
      ( ( ~ r1_lattice3(X36,X38,X39)
        | r1_lattice3(X36,X37,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ r1_tarski(X37,X38)
        | ~ l1_orders_2(X36) )
      & ( ~ r2_lattice3(X36,X38,X39)
        | r2_lattice3(X36,X37,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ r1_tarski(X37,X38)
        | ~ l1_orders_2(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).

cnf(c_0_32,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk7_4(esk3_0,X2,X3,esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X2))
    | ~ epred2_3(X3,X2,esk3_0)
    | ~ r2_hidden(esk1_3(esk3_0,X1,esk6_0),X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

fof(c_0_33,plain,(
    ! [X21,X22,X23,X24] :
      ( ( r2_lattice3(X21,X22,X23)
        | X23 != k1_yellow_0(X21,X22)
        | ~ r1_yellow_0(X21,X22)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ l1_orders_2(X21) )
      & ( ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ r2_lattice3(X21,X22,X24)
        | r1_orders_2(X21,X23,X24)
        | X23 != k1_yellow_0(X21,X22)
        | ~ r1_yellow_0(X21,X22)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ l1_orders_2(X21) )
      & ( m1_subset_1(esk2_3(X21,X22,X23),u1_struct_0(X21))
        | ~ r2_lattice3(X21,X22,X23)
        | X23 = k1_yellow_0(X21,X22)
        | ~ r1_yellow_0(X21,X22)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ l1_orders_2(X21) )
      & ( r2_lattice3(X21,X22,esk2_3(X21,X22,X23))
        | ~ r2_lattice3(X21,X22,X23)
        | X23 = k1_yellow_0(X21,X22)
        | ~ r1_yellow_0(X21,X22)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ l1_orders_2(X21) )
      & ( ~ r1_orders_2(X21,X23,esk2_3(X21,X22,X23))
        | ~ r2_lattice3(X21,X22,X23)
        | X23 = k1_yellow_0(X21,X22)
        | ~ r1_yellow_0(X21,X22)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

cnf(c_0_34,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk6_0))) = esk1_3(esk3_0,X1,esk6_0)
    | r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r2_hidden(esk1_3(esk3_0,X1,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_21]),c_0_22])])).

cnf(c_0_36,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk6_0)))
    | r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r2_hidden(esk1_3(esk3_0,X1,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_37,plain,
    ( r2_lattice3(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(X4,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | m1_subset_1(X10,k1_zfmisc_1(X11)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_39,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(esk1_3(esk3_0,X1,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_28])).

fof(c_0_40,plain,(
    ! [X8,X9] :
      ( ( ~ r1_tarski(k1_tarski(X8),X9)
        | r2_hidden(X8,X9) )
      & ( ~ r2_hidden(X8,X9)
        | r1_tarski(k1_tarski(X8),X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_41,plain,(
    ! [X6] : k2_tarski(X6,X6) = k1_tarski(X6) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_42,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0))) = esk1_3(esk3_0,esk5_0,esk6_0)
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_35])).

fof(c_0_45,plain,(
    ! [X26,X27] :
      ( ~ l1_orders_2(X26)
      | m1_subset_1(k1_yellow_0(X26,X27),u1_struct_0(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_46,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r2_lattice3(esk3_0,X2,esk6_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_21]),c_0_22])])).

cnf(c_0_47,negated_conjecture,
    ( r2_lattice3(esk3_0,esk4_0,esk6_0)
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_35])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk3_0,X1,X2)
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | X1 != esk1_3(esk3_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_22])]),c_0_44])).

cnf(c_0_53,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0)
    | r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( r1_tarski(k2_tarski(X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_57,plain,(
    ! [X15] : v1_finset_1(k1_tarski(X15)) ),
    inference(variable_rename,[status(thm)],[fc1_finset_1])).

cnf(c_0_58,negated_conjecture,
    ( r1_orders_2(esk3_0,k1_yellow_0(esk3_0,X1),X2)
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,X1) != esk1_3(esk3_0,esk5_0,esk6_0)
    | ~ r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_22])])).

cnf(c_0_59,negated_conjecture,
    ( r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)
    | r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_61,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_63,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | r1_tarski(k2_tarski(esk1_3(esk3_0,X1,esk6_0),esk1_3(esk3_0,X1,esk6_0)),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_35])).

cnf(c_0_64,plain,
    ( v1_finset_1(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( r1_orders_2(esk3_0,k1_yellow_0(esk3_0,X1),esk6_0)
    | r2_lattice3(esk3_0,esk5_0,esk6_0)
    | k1_yellow_0(esk3_0,X1) != esk1_3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_21]),c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,esk1_3(esk3_0,X1,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_21]),c_0_22])])).

cnf(c_0_67,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r2_lattice3(X1,X4,X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k1_yellow_0(X1,X2),X4) ),
    inference(spm,[status(thm)],[c_0_61,c_0_53])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k1_yellow_0(X3,X1),X4)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred2_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_69,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | m1_subset_1(k2_tarski(esk1_3(esk3_0,X1,esk6_0),esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,plain,
    ( v1_finset_1(k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_51])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_lattice3(esk3_0,esk4_0,esk6_0)
    | ~ r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_72,negated_conjecture,
    ( r2_lattice3(esk3_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_43]),c_0_66])).

fof(c_0_73,plain,(
    ! [X12,X13,X14] :
      ( ~ r2_hidden(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X14))
      | m1_subset_1(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_74,plain,(
    ! [X1,X4,X3,X2] :
      ( epred1_4(X2,X3,X4,X1)
    <=> ( ( r1_lattice3(X1,k2_tarski(X3,X4),X2)
         => ( r1_orders_2(X1,X2,X3)
            & r1_orders_2(X1,X2,X4) ) )
        & ( ( r1_orders_2(X1,X2,X3)
            & r1_orders_2(X1,X2,X4) )
         => r1_lattice3(X1,k2_tarski(X3,X4),X2) )
        & ( r2_lattice3(X1,k2_tarski(X3,X4),X2)
         => ( r1_orders_2(X1,X3,X2)
            & r1_orders_2(X1,X4,X2) ) )
        & ( ( r1_orders_2(X1,X3,X2)
            & r1_orders_2(X1,X4,X2) )
         => r2_lattice3(X1,k2_tarski(X3,X4),X2) ) ) ) ),
    introduced(definition)).

fof(c_0_75,plain,(
    ! [X28,X29,X30,X31] :
      ( ( ~ r1_lattice3(X28,X31,X30)
        | r1_lattice3(X28,X31,X29)
        | ~ r1_orders_2(X28,X29,X30)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ v4_orders_2(X28)
        | ~ l1_orders_2(X28) )
      & ( ~ r2_lattice3(X28,X31,X29)
        | r2_lattice3(X28,X31,X30)
        | ~ r1_orders_2(X28,X29,X30)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ v4_orders_2(X28)
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_yellow_0])])])])).

cnf(c_0_76,negated_conjecture,
    ( r1_orders_2(esk3_0,k1_yellow_0(esk3_0,X1),esk6_0)
    | ~ r2_lattice3(esk3_0,X2,esk6_0)
    | ~ r2_hidden(k1_yellow_0(esk3_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_21]),c_0_22])])).

cnf(c_0_77,negated_conjecture,
    ( k2_tarski(esk1_3(esk3_0,X1,esk6_0),esk1_3(esk3_0,X1,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,X1,esk6_0)
    | r2_hidden(k1_yellow_0(X2,k2_tarski(esk1_3(esk3_0,X1,esk6_0),esk1_3(esk3_0,X1,esk6_0))),X3)
    | ~ epred2_3(X3,X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_lattice3(esk3_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72])])).

cnf(c_0_79,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_81,plain,
    ( X1 = k1_xboole_0
    | r1_yellow_0(X3,X1)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred2_3(X4,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_82,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => epred1_4(X2,X3,X4,X1) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t8_yellow_0,c_0_74])).

cnf(c_0_83,plain,
    ( r2_lattice3(X1,X2,X4)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_85,negated_conjecture,
    ( r1_orders_2(esk3_0,k1_yellow_0(esk3_0,X1),esk6_0)
    | ~ r2_hidden(k1_yellow_0(esk3_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_72])).

cnf(c_0_86,negated_conjecture,
    ( k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_hidden(k1_yellow_0(esk3_0,k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_28]),c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_88,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_89,plain,
    ( k2_tarski(esk1_3(esk3_0,X1,esk6_0),esk1_3(esk3_0,X1,esk6_0)) = k1_xboole_0
    | r1_yellow_0(X2,k2_tarski(esk1_3(esk3_0,X1,esk6_0),esk1_3(esk3_0,X1,esk6_0)))
    | r2_lattice3(esk3_0,X1,esk6_0)
    | ~ epred2_3(X3,X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_69]),c_0_70])])).

fof(c_0_90,plain,(
    ! [X32,X33,X34,X35] :
      ( ~ l1_orders_2(X32)
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | ~ m1_subset_1(X34,u1_struct_0(X32))
      | ~ m1_subset_1(X35,u1_struct_0(X32))
      | epred1_4(X33,X34,X35,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_82])])])).

fof(c_0_91,plain,(
    ! [X1,X4,X3,X2] :
      ( epred1_4(X2,X3,X4,X1)
     => ( ( r1_lattice3(X1,k2_tarski(X3,X4),X2)
         => ( r1_orders_2(X1,X2,X3)
            & r1_orders_2(X1,X2,X4) ) )
        & ( ( r1_orders_2(X1,X2,X3)
            & r1_orders_2(X1,X2,X4) )
         => r1_lattice3(X1,k2_tarski(X3,X4),X2) )
        & ( r2_lattice3(X1,k2_tarski(X3,X4),X2)
         => ( r1_orders_2(X1,X3,X2)
            & r1_orders_2(X1,X4,X2) ) )
        & ( ( r1_orders_2(X1,X3,X2)
            & r1_orders_2(X1,X4,X2) )
         => r2_lattice3(X1,k2_tarski(X3,X4),X2) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_74])).

cnf(c_0_92,negated_conjecture,
    ( r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r1_orders_2(esk3_0,X2,esk6_0)
    | ~ r2_lattice3(esk3_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_21]),c_0_84]),c_0_22])])).

cnf(c_0_93,negated_conjecture,
    ( k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,k1_yellow_0(esk3_0,k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | m1_subset_1(k1_yellow_0(esk3_0,k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_86])).

cnf(c_0_95,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_88]),c_0_53])).

cnf(c_0_96,negated_conjecture,
    ( k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_yellow_0(esk3_0,k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_28]),c_0_78])).

cnf(c_0_97,plain,
    ( epred1_4(X2,X3,X4,X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

fof(c_0_98,plain,(
    ! [X44,X45,X46,X47] :
      ( ( r1_orders_2(X44,X47,X46)
        | ~ r1_lattice3(X44,k2_tarski(X46,X45),X47)
        | ~ epred1_4(X47,X46,X45,X44) )
      & ( r1_orders_2(X44,X47,X45)
        | ~ r1_lattice3(X44,k2_tarski(X46,X45),X47)
        | ~ epred1_4(X47,X46,X45,X44) )
      & ( ~ r1_orders_2(X44,X47,X46)
        | ~ r1_orders_2(X44,X47,X45)
        | r1_lattice3(X44,k2_tarski(X46,X45),X47)
        | ~ epred1_4(X47,X46,X45,X44) )
      & ( r1_orders_2(X44,X46,X47)
        | ~ r2_lattice3(X44,k2_tarski(X46,X45),X47)
        | ~ epred1_4(X47,X46,X45,X44) )
      & ( r1_orders_2(X44,X45,X47)
        | ~ r2_lattice3(X44,k2_tarski(X46,X45),X47)
        | ~ epred1_4(X47,X46,X45,X44) )
      & ( ~ r1_orders_2(X44,X46,X47)
        | ~ r1_orders_2(X44,X45,X47)
        | r2_lattice3(X44,k2_tarski(X46,X45),X47)
        | ~ epred1_4(X47,X46,X45,X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_91])])])).

cnf(c_0_99,negated_conjecture,
    ( k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,X1,esk6_0)
    | ~ r2_lattice3(esk3_0,X1,k1_yellow_0(esk3_0,k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_100,negated_conjecture,
    ( k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)),k1_yellow_0(esk3_0,k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_22])])).

cnf(c_0_101,negated_conjecture,
    ( epred1_4(X1,X2,esk1_3(esk3_0,X3,esk6_0),esk3_0)
    | r2_lattice3(esk3_0,X3,esk6_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_24]),c_0_22])])).

fof(c_0_102,plain,(
    ! [X7] : ~ v1_xboole_0(k1_tarski(X7)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_103,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_lattice3(X1,k2_tarski(X2,X4),X3)
    | ~ epred1_4(X3,X2,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r2_lattice3(esk3_0,k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( epred1_4(X1,esk1_3(esk3_0,X2,esk6_0),esk1_3(esk3_0,X3,esk6_0),esk3_0)
    | r2_lattice3(esk3_0,X2,esk6_0)
    | r2_lattice3(esk3_0,X3,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_24])).

cnf(c_0_106,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_107,plain,
    ( k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)
    | ~ epred1_4(esk6_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_108,negated_conjecture,
    ( epred1_4(esk6_0,esk1_3(esk3_0,X1,esk6_0),esk1_3(esk3_0,X2,esk6_0),esk3_0)
    | r2_lattice3(esk3_0,X2,esk6_0)
    | r2_lattice3(esk3_0,X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_21])).

cnf(c_0_109,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_106,c_0_51])).

cnf(c_0_110,negated_conjecture,
    ( k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)) = k1_xboole_0
    | r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_78])).

cnf(c_0_111,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_112,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_111])])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_112]),c_0_78]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:23:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.43  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.18/0.43  # and selection function SelectNewComplexAHP.
% 0.18/0.43  #
% 0.18/0.43  # Preprocessing time       : 0.029 s
% 0.18/0.43  # Presaturation interreduction done
% 0.18/0.43  
% 0.18/0.43  # Proof found!
% 0.18/0.43  # SZS status Theorem
% 0.18/0.43  # SZS output start CNFRefutation
% 0.18/0.43  fof(t52_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)<=>r2_lattice3(X1,X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_waybel_0)).
% 0.18/0.43  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 0.18/0.43  fof(t9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X1,X2,X4))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_0)).
% 0.18/0.43  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.18/0.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.43  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.18/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.43  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.18/0.43  fof(fc1_finset_1, axiom, ![X1]:v1_finset_1(k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_finset_1)).
% 0.18/0.43  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.18/0.43  fof(t4_yellow_0, axiom, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)=>![X4]:((r1_lattice3(X1,X4,X3)=>r1_lattice3(X1,X4,X2))&(r2_lattice3(X1,X4,X2)=>r2_lattice3(X1,X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_0)).
% 0.18/0.43  fof(t8_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((((r1_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4)))&((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4))=>r1_lattice3(X1,k2_tarski(X3,X4),X2)))&(r2_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))))&((r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))=>r2_lattice3(X1,k2_tarski(X3,X4),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_yellow_0)).
% 0.18/0.43  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.18/0.43  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.18/0.43  fof(c_0_14, plain, ![X1, X2, X3]:(epred2_3(X3,X2,X1)<=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))), introduced(definition)).
% 0.18/0.43  fof(c_0_15, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(epred2_3(X3,X2,X1)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)<=>r2_lattice3(X1,X3,X4)))))))), inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t52_waybel_0]), c_0_14])).
% 0.18/0.43  fof(c_0_16, plain, ![X1, X2, X3]:(epred2_3(X3,X2,X1)=>((![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r1_yellow_0(X1,X4)))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>~((r2_hidden(X4,X3)&![X5]:((v1_finset_1(X5)&m1_subset_1(X5,k1_zfmisc_1(X2)))=>~((r1_yellow_0(X1,X5)&X4=k1_yellow_0(X1,X5))))))))&![X4]:((v1_finset_1(X4)&m1_subset_1(X4,k1_zfmisc_1(X2)))=>(X4!=k1_xboole_0=>r2_hidden(k1_yellow_0(X1,X4),X3))))), inference(split_equiv,[status(thm)],[c_0_14])).
% 0.18/0.43  fof(c_0_17, plain, ![X16, X17, X18, X19]:((~r2_lattice3(X16,X17,X18)|(~m1_subset_1(X19,u1_struct_0(X16))|(~r2_hidden(X19,X17)|r1_orders_2(X16,X19,X18)))|~m1_subset_1(X18,u1_struct_0(X16))|~l1_orders_2(X16))&((m1_subset_1(esk1_3(X16,X17,X18),u1_struct_0(X16))|r2_lattice3(X16,X17,X18)|~m1_subset_1(X18,u1_struct_0(X16))|~l1_orders_2(X16))&((r2_hidden(esk1_3(X16,X17,X18),X17)|r2_lattice3(X16,X17,X18)|~m1_subset_1(X18,u1_struct_0(X16))|~l1_orders_2(X16))&(~r1_orders_2(X16,esk1_3(X16,X17,X18),X18)|r2_lattice3(X16,X17,X18)|~m1_subset_1(X18,u1_struct_0(X16))|~l1_orders_2(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.18/0.43  fof(c_0_18, negated_conjecture, ((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(epred2_3(esk5_0,esk4_0,esk3_0)&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&((~r2_lattice3(esk3_0,esk4_0,esk6_0)|~r2_lattice3(esk3_0,esk5_0,esk6_0))&(r2_lattice3(esk3_0,esk4_0,esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.18/0.43  fof(c_0_19, plain, ![X48, X49, X50, X51, X52, X54]:(((~v1_finset_1(X51)|~m1_subset_1(X51,k1_zfmisc_1(X49))|(X51=k1_xboole_0|r1_yellow_0(X48,X51))|~epred2_3(X50,X49,X48))&(((v1_finset_1(esk7_4(X48,X49,X50,X52))|~r2_hidden(X52,X50)|~m1_subset_1(X52,u1_struct_0(X48))|~epred2_3(X50,X49,X48))&(m1_subset_1(esk7_4(X48,X49,X50,X52),k1_zfmisc_1(X49))|~r2_hidden(X52,X50)|~m1_subset_1(X52,u1_struct_0(X48))|~epred2_3(X50,X49,X48)))&((r1_yellow_0(X48,esk7_4(X48,X49,X50,X52))|~r2_hidden(X52,X50)|~m1_subset_1(X52,u1_struct_0(X48))|~epred2_3(X50,X49,X48))&(X52=k1_yellow_0(X48,esk7_4(X48,X49,X50,X52))|~r2_hidden(X52,X50)|~m1_subset_1(X52,u1_struct_0(X48))|~epred2_3(X50,X49,X48)))))&(~v1_finset_1(X54)|~m1_subset_1(X54,k1_zfmisc_1(X49))|(X54=k1_xboole_0|r2_hidden(k1_yellow_0(X48,X54),X50))|~epred2_3(X50,X49,X48))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])])).
% 0.18/0.43  cnf(c_0_20, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.43  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.43  cnf(c_0_22, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.43  cnf(c_0_23, plain, (X1=k1_yellow_0(X2,esk7_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|~m1_subset_1(X1,u1_struct_0(X2))|~epred2_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.43  cnf(c_0_24, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk1_3(esk3_0,X1,esk6_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.18/0.43  cnf(c_0_25, plain, (r1_yellow_0(X1,esk7_4(X1,X2,X3,X4))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred2_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.43  cnf(c_0_26, plain, (m1_subset_1(esk7_4(X1,X2,X3,X4),k1_zfmisc_1(X2))|~r2_hidden(X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~epred2_3(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.43  cnf(c_0_27, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,X3,esk6_0)))=esk1_3(esk3_0,X3,esk6_0)|r2_lattice3(esk3_0,X3,esk6_0)|~epred2_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,X3,esk6_0),X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.18/0.43  cnf(c_0_28, negated_conjecture, (epred2_3(esk5_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.43  cnf(c_0_29, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.43  cnf(c_0_30, negated_conjecture, (r1_yellow_0(esk3_0,esk7_4(esk3_0,X1,X2,esk1_3(esk3_0,X3,esk6_0)))|r2_lattice3(esk3_0,X3,esk6_0)|~epred2_3(X2,X1,esk3_0)|~r2_hidden(esk1_3(esk3_0,X3,esk6_0),X2)), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.18/0.43  fof(c_0_31, plain, ![X36, X37, X38, X39]:((~r1_lattice3(X36,X38,X39)|r1_lattice3(X36,X37,X39)|~m1_subset_1(X39,u1_struct_0(X36))|~r1_tarski(X37,X38)|~l1_orders_2(X36))&(~r2_lattice3(X36,X38,X39)|r2_lattice3(X36,X37,X39)|~m1_subset_1(X39,u1_struct_0(X36))|~r1_tarski(X37,X38)|~l1_orders_2(X36))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).
% 0.18/0.43  cnf(c_0_32, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk7_4(esk3_0,X2,X3,esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X2))|~epred2_3(X3,X2,esk3_0)|~r2_hidden(esk1_3(esk3_0,X1,esk6_0),X3)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.18/0.43  fof(c_0_33, plain, ![X21, X22, X23, X24]:(((r2_lattice3(X21,X22,X23)|X23!=k1_yellow_0(X21,X22)|~r1_yellow_0(X21,X22)|~m1_subset_1(X23,u1_struct_0(X21))|~l1_orders_2(X21))&(~m1_subset_1(X24,u1_struct_0(X21))|(~r2_lattice3(X21,X22,X24)|r1_orders_2(X21,X23,X24))|X23!=k1_yellow_0(X21,X22)|~r1_yellow_0(X21,X22)|~m1_subset_1(X23,u1_struct_0(X21))|~l1_orders_2(X21)))&((m1_subset_1(esk2_3(X21,X22,X23),u1_struct_0(X21))|~r2_lattice3(X21,X22,X23)|X23=k1_yellow_0(X21,X22)|~r1_yellow_0(X21,X22)|~m1_subset_1(X23,u1_struct_0(X21))|~l1_orders_2(X21))&((r2_lattice3(X21,X22,esk2_3(X21,X22,X23))|~r2_lattice3(X21,X22,X23)|X23=k1_yellow_0(X21,X22)|~r1_yellow_0(X21,X22)|~m1_subset_1(X23,u1_struct_0(X21))|~l1_orders_2(X21))&(~r1_orders_2(X21,X23,esk2_3(X21,X22,X23))|~r2_lattice3(X21,X22,X23)|X23=k1_yellow_0(X21,X22)|~r1_yellow_0(X21,X22)|~m1_subset_1(X23,u1_struct_0(X21))|~l1_orders_2(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.18/0.43  cnf(c_0_34, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk6_0)))=esk1_3(esk3_0,X1,esk6_0)|r2_lattice3(esk3_0,X1,esk6_0)|~r2_hidden(esk1_3(esk3_0,X1,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.18/0.43  cnf(c_0_35, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r2_hidden(esk1_3(esk3_0,X1,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_21]), c_0_22])])).
% 0.18/0.43  cnf(c_0_36, negated_conjecture, (r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk6_0)))|r2_lattice3(esk3_0,X1,esk6_0)|~r2_hidden(esk1_3(esk3_0,X1,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_28])).
% 0.18/0.43  cnf(c_0_37, plain, (r2_lattice3(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(X4,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.43  fof(c_0_38, plain, ![X10, X11]:((~m1_subset_1(X10,k1_zfmisc_1(X11))|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|m1_subset_1(X10,k1_zfmisc_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.43  cnf(c_0_39, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(esk4_0))|~r2_hidden(esk1_3(esk3_0,X1,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_28])).
% 0.18/0.43  fof(c_0_40, plain, ![X8, X9]:((~r1_tarski(k1_tarski(X8),X9)|r2_hidden(X8,X9))&(~r2_hidden(X8,X9)|r1_tarski(k1_tarski(X8),X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.18/0.43  fof(c_0_41, plain, ![X6]:k2_tarski(X6,X6)=k1_tarski(X6), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.43  cnf(c_0_42, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.43  cnf(c_0_43, negated_conjecture, (k1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))=esk1_3(esk3_0,esk5_0,esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.18/0.43  cnf(c_0_44, negated_conjecture, (r1_yellow_0(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)))|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_36, c_0_35])).
% 0.18/0.43  fof(c_0_45, plain, ![X26, X27]:(~l1_orders_2(X26)|m1_subset_1(k1_yellow_0(X26,X27),u1_struct_0(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.18/0.43  cnf(c_0_46, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|~r2_lattice3(esk3_0,X2,esk6_0)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_21]), c_0_22])])).
% 0.18/0.43  cnf(c_0_47, negated_conjecture, (r2_lattice3(esk3_0,esk4_0,esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.43  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.43  cnf(c_0_49, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|m1_subset_1(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_39, c_0_35])).
% 0.18/0.43  cnf(c_0_50, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.18/0.43  cnf(c_0_51, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.18/0.43  cnf(c_0_52, negated_conjecture, (r1_orders_2(esk3_0,X1,X2)|r2_lattice3(esk3_0,esk5_0,esk6_0)|X1!=esk1_3(esk3_0,esk5_0,esk6_0)|~r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),X2)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_22])]), c_0_44])).
% 0.18/0.43  cnf(c_0_53, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.43  cnf(c_0_54, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r2_lattice3(esk3_0,X1,esk6_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.18/0.43  cnf(c_0_55, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)|r1_tarski(esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk4_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.18/0.43  cnf(c_0_56, plain, (r1_tarski(k2_tarski(X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.18/0.43  fof(c_0_57, plain, ![X15]:v1_finset_1(k1_tarski(X15)), inference(variable_rename,[status(thm)],[fc1_finset_1])).
% 0.18/0.43  cnf(c_0_58, negated_conjecture, (r1_orders_2(esk3_0,k1_yellow_0(esk3_0,X1),X2)|r2_lattice3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,X1)!=esk1_3(esk3_0,esk5_0,esk6_0)|~r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_22])])).
% 0.18/0.43  cnf(c_0_59, negated_conjecture, (r2_lattice3(esk3_0,esk7_4(esk3_0,esk4_0,esk5_0,esk1_3(esk3_0,esk5_0,esk6_0)),esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.18/0.43  cnf(c_0_60, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.43  cnf(c_0_61, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.43  cnf(c_0_62, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.43  cnf(c_0_63, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|r1_tarski(k2_tarski(esk1_3(esk3_0,X1,esk6_0),esk1_3(esk3_0,X1,esk6_0)),X1)), inference(spm,[status(thm)],[c_0_56, c_0_35])).
% 0.18/0.43  cnf(c_0_64, plain, (v1_finset_1(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.18/0.43  cnf(c_0_65, negated_conjecture, (r1_orders_2(esk3_0,k1_yellow_0(esk3_0,X1),esk6_0)|r2_lattice3(esk3_0,esk5_0,esk6_0)|k1_yellow_0(esk3_0,X1)!=esk1_3(esk3_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_21]), c_0_59])).
% 0.18/0.43  cnf(c_0_66, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,esk1_3(esk3_0,X1,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_21]), c_0_22])])).
% 0.18/0.43  cnf(c_0_67, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r2_lattice3(X1,X4,X3)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(k1_yellow_0(X1,X2),X4)), inference(spm,[status(thm)],[c_0_61, c_0_53])).
% 0.18/0.43  cnf(c_0_68, plain, (X1=k1_xboole_0|r2_hidden(k1_yellow_0(X3,X1),X4)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred2_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.43  cnf(c_0_69, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|m1_subset_1(k2_tarski(esk1_3(esk3_0,X1,esk6_0),esk1_3(esk3_0,X1,esk6_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.18/0.43  cnf(c_0_70, plain, (v1_finset_1(k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_64, c_0_51])).
% 0.18/0.43  cnf(c_0_71, negated_conjecture, (~r2_lattice3(esk3_0,esk4_0,esk6_0)|~r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.43  cnf(c_0_72, negated_conjecture, (r2_lattice3(esk3_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_43]), c_0_66])).
% 0.18/0.43  fof(c_0_73, plain, ![X12, X13, X14]:(~r2_hidden(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X14))|m1_subset_1(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.18/0.43  fof(c_0_74, plain, ![X1, X4, X3, X2]:(epred1_4(X2,X3,X4,X1)<=>((((r1_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4)))&((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4))=>r1_lattice3(X1,k2_tarski(X3,X4),X2)))&(r2_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))))&((r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))=>r2_lattice3(X1,k2_tarski(X3,X4),X2)))), introduced(definition)).
% 0.18/0.43  fof(c_0_75, plain, ![X28, X29, X30, X31]:((~r1_lattice3(X28,X31,X30)|r1_lattice3(X28,X31,X29)|~r1_orders_2(X28,X29,X30)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|(~v4_orders_2(X28)|~l1_orders_2(X28)))&(~r2_lattice3(X28,X31,X29)|r2_lattice3(X28,X31,X30)|~r1_orders_2(X28,X29,X30)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|(~v4_orders_2(X28)|~l1_orders_2(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_yellow_0])])])])).
% 0.18/0.44  cnf(c_0_76, negated_conjecture, (r1_orders_2(esk3_0,k1_yellow_0(esk3_0,X1),esk6_0)|~r2_lattice3(esk3_0,X2,esk6_0)|~r2_hidden(k1_yellow_0(esk3_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_21]), c_0_22])])).
% 0.18/0.44  cnf(c_0_77, negated_conjecture, (k2_tarski(esk1_3(esk3_0,X1,esk6_0),esk1_3(esk3_0,X1,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,X1,esk6_0)|r2_hidden(k1_yellow_0(X2,k2_tarski(esk1_3(esk3_0,X1,esk6_0),esk1_3(esk3_0,X1,esk6_0))),X3)|~epred2_3(X3,X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])])).
% 0.18/0.44  cnf(c_0_78, negated_conjecture, (~r2_lattice3(esk3_0,esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72])])).
% 0.18/0.44  cnf(c_0_79, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.18/0.44  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.44  cnf(c_0_81, plain, (X1=k1_xboole_0|r1_yellow_0(X3,X1)|~v1_finset_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~epred2_3(X4,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.44  fof(c_0_82, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>epred1_4(X2,X3,X4,X1))))), inference(apply_def,[status(thm)],[t8_yellow_0, c_0_74])).
% 0.18/0.44  cnf(c_0_83, plain, (r2_lattice3(X1,X2,X4)|~r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.18/0.44  cnf(c_0_84, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.44  cnf(c_0_85, negated_conjecture, (r1_orders_2(esk3_0,k1_yellow_0(esk3_0,X1),esk6_0)|~r2_hidden(k1_yellow_0(esk3_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_76, c_0_72])).
% 0.18/0.44  cnf(c_0_86, negated_conjecture, (k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_hidden(k1_yellow_0(esk3_0,k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_28]), c_0_78])).
% 0.18/0.44  cnf(c_0_87, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.18/0.44  cnf(c_0_88, plain, (r2_lattice3(X1,X2,X3)|X3!=k1_yellow_0(X1,X2)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.44  cnf(c_0_89, plain, (k2_tarski(esk1_3(esk3_0,X1,esk6_0),esk1_3(esk3_0,X1,esk6_0))=k1_xboole_0|r1_yellow_0(X2,k2_tarski(esk1_3(esk3_0,X1,esk6_0),esk1_3(esk3_0,X1,esk6_0)))|r2_lattice3(esk3_0,X1,esk6_0)|~epred2_3(X3,X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_69]), c_0_70])])).
% 0.18/0.44  fof(c_0_90, plain, ![X32, X33, X34, X35]:(~l1_orders_2(X32)|(~m1_subset_1(X33,u1_struct_0(X32))|(~m1_subset_1(X34,u1_struct_0(X32))|(~m1_subset_1(X35,u1_struct_0(X32))|epred1_4(X33,X34,X35,X32))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_82])])])).
% 0.18/0.44  fof(c_0_91, plain, ![X1, X4, X3, X2]:(epred1_4(X2,X3,X4,X1)=>((((r1_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4)))&((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4))=>r1_lattice3(X1,k2_tarski(X3,X4),X2)))&(r2_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))))&((r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))=>r2_lattice3(X1,k2_tarski(X3,X4),X2)))), inference(split_equiv,[status(thm)],[c_0_74])).
% 0.18/0.44  cnf(c_0_92, negated_conjecture, (r2_lattice3(esk3_0,X1,esk6_0)|~r1_orders_2(esk3_0,X2,esk6_0)|~r2_lattice3(esk3_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_21]), c_0_84]), c_0_22])])).
% 0.18/0.44  cnf(c_0_93, negated_conjecture, (k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,k1_yellow_0(esk3_0,k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))),esk6_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.18/0.44  cnf(c_0_94, negated_conjecture, (k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|m1_subset_1(k1_yellow_0(esk3_0,k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_87, c_0_86])).
% 0.18/0.44  cnf(c_0_95, plain, (r2_lattice3(X1,X2,k1_yellow_0(X1,X2))|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_88]), c_0_53])).
% 0.18/0.44  cnf(c_0_96, negated_conjecture, (k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_yellow_0(esk3_0,k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_28]), c_0_78])).
% 0.18/0.44  cnf(c_0_97, plain, (epred1_4(X2,X3,X4,X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.18/0.44  fof(c_0_98, plain, ![X44, X45, X46, X47]:(((((r1_orders_2(X44,X47,X46)|~r1_lattice3(X44,k2_tarski(X46,X45),X47)|~epred1_4(X47,X46,X45,X44))&(r1_orders_2(X44,X47,X45)|~r1_lattice3(X44,k2_tarski(X46,X45),X47)|~epred1_4(X47,X46,X45,X44)))&(~r1_orders_2(X44,X47,X46)|~r1_orders_2(X44,X47,X45)|r1_lattice3(X44,k2_tarski(X46,X45),X47)|~epred1_4(X47,X46,X45,X44)))&((r1_orders_2(X44,X46,X47)|~r2_lattice3(X44,k2_tarski(X46,X45),X47)|~epred1_4(X47,X46,X45,X44))&(r1_orders_2(X44,X45,X47)|~r2_lattice3(X44,k2_tarski(X46,X45),X47)|~epred1_4(X47,X46,X45,X44))))&(~r1_orders_2(X44,X46,X47)|~r1_orders_2(X44,X45,X47)|r2_lattice3(X44,k2_tarski(X46,X45),X47)|~epred1_4(X47,X46,X45,X44))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_91])])])).
% 0.18/0.44  cnf(c_0_99, negated_conjecture, (k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,X1,esk6_0)|~r2_lattice3(esk3_0,X1,k1_yellow_0(esk3_0,k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])).
% 0.18/0.44  cnf(c_0_100, negated_conjecture, (k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)),k1_yellow_0(esk3_0,k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_22])])).
% 0.18/0.44  cnf(c_0_101, negated_conjecture, (epred1_4(X1,X2,esk1_3(esk3_0,X3,esk6_0),esk3_0)|r2_lattice3(esk3_0,X3,esk6_0)|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_24]), c_0_22])])).
% 0.18/0.44  fof(c_0_102, plain, ![X7]:~v1_xboole_0(k1_tarski(X7)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.18/0.44  cnf(c_0_103, plain, (r1_orders_2(X1,X2,X3)|~r2_lattice3(X1,k2_tarski(X2,X4),X3)|~epred1_4(X3,X2,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.18/0.44  cnf(c_0_104, negated_conjecture, (k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r2_lattice3(esk3_0,k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.18/0.44  cnf(c_0_105, negated_conjecture, (epred1_4(X1,esk1_3(esk3_0,X2,esk6_0),esk1_3(esk3_0,X3,esk6_0),esk3_0)|r2_lattice3(esk3_0,X2,esk6_0)|r2_lattice3(esk3_0,X3,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_101, c_0_24])).
% 0.18/0.44  cnf(c_0_106, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.18/0.44  cnf(c_0_107, plain, (k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)|~epred1_4(esk6_0,esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0),esk3_0)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.18/0.44  cnf(c_0_108, negated_conjecture, (epred1_4(esk6_0,esk1_3(esk3_0,X1,esk6_0),esk1_3(esk3_0,X2,esk6_0),esk3_0)|r2_lattice3(esk3_0,X2,esk6_0)|r2_lattice3(esk3_0,X1,esk6_0)), inference(spm,[status(thm)],[c_0_105, c_0_21])).
% 0.18/0.44  cnf(c_0_109, plain, (~v1_xboole_0(k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_106, c_0_51])).
% 0.18/0.44  cnf(c_0_110, negated_conjecture, (k2_tarski(esk1_3(esk3_0,esk4_0,esk6_0),esk1_3(esk3_0,esk4_0,esk6_0))=k1_xboole_0|r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_78])).
% 0.18/0.44  cnf(c_0_111, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.18/0.44  cnf(c_0_112, negated_conjecture, (r1_orders_2(esk3_0,esk1_3(esk3_0,esk4_0,esk6_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_111])])).
% 0.18/0.44  cnf(c_0_113, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_112]), c_0_78]), ['proof']).
% 0.18/0.44  # SZS output end CNFRefutation
% 0.18/0.44  # Proof object total steps             : 114
% 0.18/0.44  # Proof object clause steps            : 79
% 0.18/0.44  # Proof object formula steps           : 35
% 0.18/0.44  # Proof object conjectures             : 51
% 0.18/0.44  # Proof object clause conjectures      : 48
% 0.18/0.44  # Proof object formula conjectures     : 3
% 0.18/0.44  # Proof object initial clauses used    : 31
% 0.18/0.44  # Proof object initial formulas used   : 14
% 0.18/0.44  # Proof object generating inferences   : 44
% 0.18/0.44  # Proof object simplifying inferences  : 41
% 0.18/0.44  # Training examples: 0 positive, 0 negative
% 0.18/0.44  # Parsed axioms                        : 14
% 0.18/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.44  # Initial clauses                      : 46
% 0.18/0.44  # Removed in clause preprocessing      : 1
% 0.18/0.44  # Initial clauses in saturation        : 45
% 0.18/0.44  # Processed clauses                    : 503
% 0.18/0.44  # ...of these trivial                  : 0
% 0.18/0.44  # ...subsumed                          : 76
% 0.18/0.44  # ...remaining for further processing  : 427
% 0.18/0.44  # Other redundant clauses eliminated   : 0
% 0.18/0.44  # Clauses deleted for lack of memory   : 0
% 0.18/0.44  # Backward-subsumed                    : 9
% 0.18/0.44  # Backward-rewritten                   : 45
% 0.18/0.44  # Generated clauses                    : 1182
% 0.18/0.44  # ...of the previous two non-trivial   : 1167
% 0.18/0.44  # Contextual simplify-reflections      : 12
% 0.18/0.44  # Paramodulations                      : 1179
% 0.18/0.44  # Factorizations                       : 0
% 0.18/0.44  # Equation resolutions                 : 3
% 0.18/0.44  # Propositional unsat checks           : 0
% 0.18/0.44  #    Propositional check models        : 0
% 0.18/0.44  #    Propositional check unsatisfiable : 0
% 0.18/0.44  #    Propositional clauses             : 0
% 0.18/0.44  #    Propositional clauses after purity: 0
% 0.18/0.44  #    Propositional unsat core size     : 0
% 0.18/0.44  #    Propositional preprocessing time  : 0.000
% 0.18/0.44  #    Propositional encoding time       : 0.000
% 0.18/0.44  #    Propositional solver time         : 0.000
% 0.18/0.44  #    Success case prop preproc time    : 0.000
% 0.18/0.44  #    Success case prop encoding time   : 0.000
% 0.18/0.44  #    Success case prop solver time     : 0.000
% 0.18/0.44  # Current number of processed clauses  : 328
% 0.18/0.44  #    Positive orientable unit clauses  : 20
% 0.18/0.44  #    Positive unorientable unit clauses: 0
% 0.18/0.44  #    Negative unit clauses             : 3
% 0.18/0.44  #    Non-unit-clauses                  : 305
% 0.18/0.44  # Current number of unprocessed clauses: 699
% 0.18/0.44  # ...number of literals in the above   : 3515
% 0.18/0.44  # Current number of archived formulas  : 0
% 0.18/0.44  # Current number of archived clauses   : 100
% 0.18/0.44  # Clause-clause subsumption calls (NU) : 22919
% 0.18/0.44  # Rec. Clause-clause subsumption calls : 5824
% 0.18/0.44  # Non-unit clause-clause subsumptions  : 97
% 0.18/0.44  # Unit Clause-clause subsumption calls : 126
% 0.18/0.44  # Rewrite failures with RHS unbound    : 0
% 0.18/0.44  # BW rewrite match attempts            : 5
% 0.18/0.44  # BW rewrite match successes           : 2
% 0.18/0.44  # Condensation attempts                : 0
% 0.18/0.44  # Condensation successes               : 0
% 0.18/0.44  # Termbank termtop insertions          : 46612
% 0.18/0.44  
% 0.18/0.44  # -------------------------------------------------
% 0.18/0.44  # User time                : 0.093 s
% 0.18/0.44  # System time              : 0.009 s
% 0.18/0.44  # Total time               : 0.102 s
% 0.18/0.44  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
